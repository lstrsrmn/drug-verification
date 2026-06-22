"""Vehicle specification loss integration for constraint-augmented training.

Loads the `safe` property from a generated training spec and returns a callable
loss function that can be combined with the standard task loss during training.

See: https://vehicle-lang.readthedocs.io/en/stable/training.html

The `safe` property has an `if Ka < Ke` branch on @parameter declarations.
The Vehicle loss compiler cannot resolve symbolic branches, so
generate_training_spec() produces a minimal temporary .vcl that inlines Ka,
Ke, Vd and the scaler values as literals, resolving the branch at generation
time.

The returned callable has the form fn(pk=network_fn) -> scalar tensor,
matching the interface expected by train_model_with_constraint.
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
    """Return a minimal .vcl spec string for safe loss compilation only.

    Inlines scaler values and PK parameters as literals so the Vehicle loss
    compiler can resolve them. The if/else branch on Ka vs Ke is resolved at
    generation time. safeOutput targets C_safe * 0.95 to provide Marabou margin.

    Args:
        mean: Scaler mean array (length 5).
        std_dev: Scaler std array (length 5).
        parameters: Dict containing Ka, Ke, Vd, C_safe, Ke_over, Ka_under,
                    Ka_over, Ke_under (matching DEFAULT_SPEC_PARAMS keys).

    Returns:
        String containing a minimal .vcl spec declaring only safe.
    """
    Ka = parameters["Ka"]
    Ke = parameters["Ke"]
    Vd = parameters["Vd"]
    C_safe = parameters["C_safe"]
    Ke_over = parameters["Ke_over"]
    Ka_under = parameters["Ka_under"]

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
-- Auto-generated training spec for safe — do not edit by hand.
-- Generated from pk.vcl with concrete parameter and scaler values inlined.
-- The if/else branch on Ka vs Ke is resolved at generation time.
-- safeOutput targets C_safe * 0.95 to provide Marabou margin.

type UnnormalisedInputVector = Tensor Real [5]
type InputVector = Tensor Real [5]
type OutputVector = Tensor Real [1]

conc   = 0
temp   = 1
wbc    = 2
age    = 3
weight = 4

@network
pk : InputVector -> OutputVector

meanVals : UnnormalisedInputVector
meanVals = [{mean_str}]

stdVals : UnnormalisedInputVector
stdVals = [{std_str}]

normalise : UnnormalisedInputVector -> InputVector
normalise x = foreach i . (x ! i - meanVals ! i) / stdVals ! i

normpk : UnnormalisedInputVector -> OutputVector
normpk x = pk (normalise x)

safeInput : UnnormalisedInputVector -> Bool
safeInput x =
    0    <= x ! conc   <= {C_safe:.8g} and
    36.5 <= x ! temp   <= 40 and
    7.5  <= x ! wbc    <= 20 and
    18   <= x ! age    <= 89 and
    50   <= x ! weight <= 100

safeOutput : UnnormalisedInputVector -> Bool
safeOutput x =
    let d = (((normpk x) ! 0) * {Ka:.8g}) / ({Vd:.8g} * ({Ka:.8g} - {Ke:.8g})) in
    (x ! conc) + d * ({peak_factor}) < {training_ceiling:.8g}

@property
safe : Bool
safe = forall x . safeInput x => safeOutput x
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

    Compiles the `safe` property from a generated temporary spec with inlined
    parameter values. The if/else branch on Ka/Ke in pk.vcl causes the loss
    compiler to collapse to a constant when loaded directly; inlining resolves
    it at generation time.

    Args:
        spec_path: Path to the main pk.vcl file (unused; kept for API compatibility).
        properties: Iterable of property names to load. Defaults to ["safe"].
        logic: Differentiable logic to use (default: Vehicle).
        mean: Scaler mean array. Required.
        std_dev: Scaler std array. Required.
        parameters: Dict of parameter values (Ka, Ke, Vd, C_safe, …).

    Returns:
        Dict mapping property name -> callable ``fn(pk=network_fn) -> tensor``.
    """
    if logic is None:
        logic = vcl.DifferentiableLogic.Vehicle

    props = list(properties) if properties else ["safe"]
    result = {}

    if "safe" in props:
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
                declarations=["safe"],
            )
        finally:
            os.unlink(tmp.name)
        result["safe"] = decls["safe"]

    return result
