"""Vehicle specification loss integration for constraint-augmented training.

Loads properties from a .vcl specification file and returns callable loss
functions that can be combined with the standard task loss during training.

See: https://vehicle-lang.readthedocs.io/en/stable/training.html
"""

import vehicle_lang as vcl
from vehicle_lang.loss import tensorflow as loss_tf

# Default parameter values matching verify.sh

def load_drug_verification_constraints(
    spec_path="pk.vcl",
    properties=None,
    logic=None,
):
    """Load Vehicle specification properties as differentiable loss functions.

    Args:
        spec_path: Path to the .vcl specification file.
        properties: Optional iterable of property names to load. If None, loads all properties.
        logic: Differentiable logic to use (default: Vehicle).

    Returns:
        Dict mapping property name -> callable loss function.
        Each loss function accepts a network callable and parameters, and returns a scalar tensor.
    """

    if logic is None:
        logic = vcl.DifferentiableLogic.Vehicle

    declarations = loss_tf.load_specification(
        spec_path,
        logic=logic,
        declarations=(),# properties or (),
    )

    # if properties:
    #     return {name: declarations[name] for name in properties if name in declarations}
    return dict(declarations)
