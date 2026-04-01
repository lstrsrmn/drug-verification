"""Vehicle specification loss integration for constraint-augmented training.

Loads properties from a .vcl specification file and returns callable loss
functions that can be combined with the standard task loss during training.

See: https://vehicle-lang.readthedocs.io/en/stable/training.html

Loading strategy (Vehicle 0.24.1+)
------------------------------------
Two properties need to be trained against: safeFar and safeNear.

  safeFar: The loss compiler cannot handle the `if Ka < Ke` branch in
    pk.vcl when Ka/Ke are @parameter declarations — it collapses to a
    constant. generate_training_spec() produces a minimal temporary .vcl
    that inlines Ka, Ke, Vd and the scaler values as literals, resolving
    the branch at spec-generation time. Per-element input bounds (fixed
    in Vehicle #1086) are used, matching the tight physiological ranges
    in safeFarInput.

  safeNear: Loads directly from pk.vcl. Vehicle 0.24.1 resolves
    @parameter declarations correctly (#1090) and handles negation through
    forall (#1098), so no generated spec is needed. The compiled function
    takes (meanScalingValues, standardDeviationValues, pk, C_safe, eps)
    as explicit arguments.

Both paths return a callable of the form fn(network) -> scalar tensor,
so the caller (cmd_train) is unaffected.
"""

import os
import tempfile

import vehicle_lang as vcl
from vehicle_lang.loss import tensorflow as loss_tf

# ── Vehicle / TensorFlow PTY workaround ────────────────────────────────────
# vehicle_lang.session.check_output uses PTY-based stdout capture to work
# around C-level stdout in the Haskell RTS.  When TensorFlow has already been
# imported (as it always is during training), the PTY capture returns an empty
# string and Vehicle fails with JSONDecodeError.  Session.check_output (the
# instance method, not the module-level function) uses redirect_stdout instead
# and is unaffected by TF's early initialisation.  We patch the module-level
# function to use that path.
try:
    from vehicle_lang.session._session import Session as _VehicleSession
    import vehicle_lang.session as _vcl_session

    def _check_output_no_pty(args):
        return _VehicleSession().__enter__().check_output(args)

    _vcl_session.check_output = _check_output_no_pty
except Exception:
    pass  # If the patch fails, fall through to the default behaviour.
# ───────────────────────────────────────────────────────────────────────────


def generate_training_spec(
    mean,
    std_dev,
    parameters: dict,
) -> str:
    """Return a .vcl spec string for training loss compilation.

    Inlines all scaler values and PK parameters as literals so the Vehicle
    loss compiler can resolve them — @dataset and @parameter free variables
    cannot be compiled. Generates both safeFar and safeNear properties.

    safeFarOutput targets C_safe * 0.95 (stricter than the verified property)
    to give Marabou a margin at verification time, preventing floating-point
    boundary counterexamples.

    Input bounds are per-element (Vehicle 0.24.1+, fix #1086):
      conc:   0 – C_safe*0.99 (safeFar domain)
      temp:   34 – 43°C (severe hypothermia to maximum survivable)
      wbc:    0 – 100 (full possible range)
      age:    0 – 100 (full possible range)
      weight: 0 – 100 (full possible range)

    Args:
        mean: Fitted StandardScaler mean array (length 5).
        std_dev: Fitted StandardScaler scale array (length 5).
        parameters: Dict matching DEFAULT_SPEC_PARAMS keys.

    Returns:
        String containing a complete .vcl spec with safeFar and safeNear.
    """
    Ka = parameters["Ka"]
    Ke = parameters["Ke"]
    Vd = parameters["Vd"]
    C_safe = parameters["C_safe"]
    Ke_over = parameters["Ke_over"]
    Ka_under = parameters["Ka_under"]
    eps = parameters["eps"]

    mean_str = ", ".join(f"{v:.8g}" for v in mean)
    std_str  = ", ".join(f"{v:.8g}" for v in std_dev)

    # Resolve the if/else branch at generation time so the compiler sees
    # a single concrete formula with no symbolic conditionals.
    if Ka >= Ke:
        peak_factor = f"{Ke_over:.8g} - {Ka_under:.8g}"
    else:
        Ka_over  = parameters["Ka_over"]
        Ke_under = parameters["Ke_under"]
        peak_factor = f"{Ke_under:.8g} - {Ka_over:.8g}"

    training_ceiling = C_safe * 0.95

    return f"""\
-- Auto-generated training spec — do not edit by hand.
-- Generated from pk.vcl with all @parameter and @dataset values inlined.
-- Uses per-element input bounds (Vehicle 0.24.1+, fix #1086).
-- safeFarOutput targets C_safe * 0.95 to provide Marabou margin.

type InputVector = Tensor Real [5]
type OutputVector = Tensor Real [1]

conc   = 0
temp   = 1
wbc    = 2
age    = 3
weight = 4

@network
pk : InputVector -> OutputVector

meanVals : InputVector
meanVals = [{mean_str}]

stdVals : InputVector
stdVals = [{std_str}]

normalise : InputVector -> InputVector
normalise x = foreach i . (x ! i - meanVals ! i) / stdVals ! i

normpk : InputVector -> OutputVector
normpk x = pk (normalise x)

safeFarInput : InputVector -> Bool
safeFarInput x =
    0 <= x ! conc <= {C_safe * 0.99:.8g} and
    34 <= x ! temp <= 43 and
    0 <= x ! wbc <= 100 and
    0 <= x ! age <= 100 and
    0 <= x ! weight <= 100

safeFarOutput : InputVector -> Bool
safeFarOutput x =
    let d = (((normpk x) ! 0) * {Ka:.8g}) / ({Vd:.8g} * ({Ka:.8g} - {Ke:.8g})) in
    (x ! conc) + d * ({peak_factor}) < {training_ceiling:.8g}

@property
safeFar : Bool
safeFar = forall x . safeFarInput x => safeFarOutput x

safeNearInput : InputVector -> Bool
safeNearInput x =
    {C_safe * 0.99:.8g} <= x ! conc <= {C_safe:.8g} and
    34 <= x ! temp <= 43 and
    0 <= x ! wbc <= 100 and
    0 <= x ! age <= 100 and
    0 <= x ! weight <= 100

@property
safeNear : Bool
safeNear = forall x . safeNearInput x => normpk x ! 0 < {eps:.8g}
"""


def load_drug_verification_constraints(
    spec_path="pk.vcl",
    properties=None,
    logic=None,
    mean=None,
    std_dev=None,
    parameters=None,
):
    """Load Vehicle specification properties as differentiable loss functions.

    Both safeFar and safeNear are compiled from a single generated training
    spec with all @parameter and @dataset values inlined. Loading from pk.vcl
    directly is not used for training because @dataset free variables cannot
    be resolved by the loss compiler.

    Args:
        spec_path: Unused for training (kept for API compatibility).
        properties: Property names to load. Defaults to ["safeFar", "safeNear"].
        logic: Differentiable logic (default: Vehicle).
        mean: Fitted scaler mean array. Required for training.
        std_dev: Fitted scaler scale array. Required for training.
        parameters: Dict matching DEFAULT_SPEC_PARAMS. Required for training.

    Returns:
        Dict mapping property name -> callable ``fn(pk=network_fn) -> tensor``.
    """
    if logic is None:
        logic = vcl.DifferentiableLogic.Vehicle

    props = list(properties) if properties else ["safeFar", "safeNear"]

    spec_content = generate_training_spec(mean, std_dev, parameters)
    tmp = tempfile.NamedTemporaryFile(
        mode="w", suffix=".vcl", delete=False, dir="."
    )
    try:
        tmp.write(spec_content)
        tmp.flush()
        tmp.close()
        decls = loss_tf.load_specification(
            tmp.name,
            logic=logic,
            declarations=props,
        )
    finally:
        os.unlink(tmp.name)

    return {name: decls[name] for name in props if name in decls}
