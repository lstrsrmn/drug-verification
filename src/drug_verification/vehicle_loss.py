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
    """Return a minimal .vcl spec string for safeFar loss compilation.

    Inlines scaler values and PK parameters as literals so the Vehicle loss
    compiler can resolve them. Uses tight per-element physiological input
    bounds matching safeFarInput in pk.vcl (supported since Vehicle #1086).
    The if/else branch on Ka vs Ke is resolved at generation time.

    Args:
        mean: Scaler mean array (length 5).
        std_dev: Scaler std array (length 5).
        parameters: Dict containing Ka, Ke, Vd, C_safe, Ke_over, Ka_under,
                    Ka_over, Ke_under (matching DEFAULT_SPEC_PARAMS keys).

    Returns:
        String containing a minimal .vcl spec declaring only safeFar.
    """
    Ka = parameters["Ka"]
    Ke = parameters["Ke"]
    Vd = parameters["Vd"]
    C_safe = parameters["C_safe"]
    Ke_over = parameters["Ke_over"]
    Ka_under = parameters["Ka_under"]

    mean_str = ", ".join(f"{v:.10f}" for v in mean)
    std_str  = ", ".join(f"{v:.10f}" for v in std_dev)

    # Resolve the if/else branch at generation time so the compiler sees
    # a single concrete formula with no symbolic conditionals.
    if Ka >= Ke:
        peak_factor = f"{Ke_over:.8g} - {Ka_under:.8g}"
    else:
        Ka_over  = parameters["Ka_over"]
        Ke_under = parameters["Ke_under"]
        peak_factor = f"{Ke_under:.8g} - {Ka_over:.8g}"

    return f"""\
-- Auto-generated training spec for safeFar — do not edit by hand.
-- Generated from pk.vcl with concrete parameter and scaler values inlined.

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
    36.5 <= x ! temp <= 40 and
    7.5 <= x ! wbc <= 20 and
    18 <= x ! age <= 89 and
    50 <= x ! weight <= 100

safeFarOutput : InputVector -> Bool
safeFarOutput x =
    let d = (((normpk x) ! 0) * {Ka:.8g}) / ({Vd:.8g} * ({Ka:.8g} - {Ke:.8g})) in
    (x ! conc) + d * ({peak_factor}) < {C_safe * 0.95:.8g}

@property
safeFar : Bool
safeFar = forall x . safeFarInput x => safeFarOutput x
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

    Uses two loading strategies depending on the property:

      safeFar: Compiled from a generated temporary spec with inlined values.
               The if/else branch on Ka/Ke in pk.vcl causes the loss compiler
               to collapse to a constant when loaded directly; inlining
               resolves it at generation time.

      safeNear: Loaded directly from pk.vcl. Vehicle 0.24.1 resolves
               @parameter declarations correctly and handles negation through
               forall. The compiled function's extra arguments (scaler arrays,
               C_safe, eps) are bound via closure so the returned callable
               only requires the network.

    Args:
        spec_path: Path to the main pk.vcl file (used for safeNear).
        properties: Iterable of property names to load. Defaults to both.
        logic: Differentiable logic to use (default: Vehicle).
        mean: Scaler mean array. Required.
        std_dev: Scaler std array. Required.
        parameters: Dict of parameter values (Ka, Ke, Vd, C_safe, eps, …).

    Returns:
        Dict mapping property name -> callable ``fn(network) -> scalar tensor``.
    """
    import tensorflow as tf
    import numpy as np

    if logic is None:
        logic = vcl.DifferentiableLogic.Vehicle

    props = list(properties) if properties else ["safeFar", "safeNear"]
    result = {}

    if "safeFar" in props:
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
                declarations=["safeFar"],
            )
        finally:
            os.unlink(tmp.name)
        result["safeFar"] = decls["safeFar"]  # fn(pk) -> loss

    if "safeNear" in props:
        decls = loss_tf.load_specification(
            spec_path,
            logic=logic,
            declarations=["safeNear"],
        )
        safe_near_raw = decls["safeNear"]
        # Bind the extra arguments so the returned callable matches fn(network) -> loss
        mean_t = tf.constant(np.array(mean), dtype=tf.float32)
        std_t  = tf.constant(np.array(std_dev), dtype=tf.float32)
        C_safe = float(parameters["C_safe"])
        eps    = float(parameters["eps"])

        def _safe_near(network_fn, _mean=mean_t, _std=std_t, _C=C_safe, _eps=eps):
            return safe_near_raw(_mean, _std, network_fn, _C, _eps)

        result["safeNear"] = _safe_near

    return result
