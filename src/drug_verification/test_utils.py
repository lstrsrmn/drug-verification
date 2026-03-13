"""Utilities for building and testing ONNX models for formal verification.

This module provides functions to generate neural network models
suitable for Marabou formal verification, with interval arithmetic
support for pharmacokinetic calculations.
"""

import torch
import torch.nn as nn
from mpmath import mp, iv

try:
    import onnxruntime as ort
    HAS_ONNXRUNTIME = True
except ImportError:
    HAS_ONNXRUNTIME = False


class MarabouFriendlyZero(nn.Module):
    """A simple neural network with zero weights for Marabou verification.
    
    This module implements a single linear layer with weights initialized
    to zero and bias to a small non-zero value (~0.0001). Designed for
    formal verification with Marabou constraint solver.
    """
    
    def __init__(self, inp_size):
        """Initialize the zero-weight model.
        
        Args:
            inp_size (int): Input dimension for the linear layer.
        """
        super().__init__()
        self.fc = nn.Linear(inp_size, 1)
        nn.init.constant_(self.fc.weight, 0)
        nn.init.constant_(self.fc.bias, 0.0001)

    def forward(self, x):
        """Forward pass through the linear layer.
        
        Args:
            x: Input tensor.
            
        Returns:
            Output tensor from the linear layer.
        """
        return self.fc(x)


def build_it(inp_size, output_path="pk.onnx"):
    """Build and export a zero-weight neural network to ONNX format.
    
    Creates a simple neural network with zero weights and small bias,
    then exports it to ONNX format. Constant folding is disabled to
    ensure that zero multiplications are visible to formal verifiers
    like Marabou (rather than being optimized away).
    
    Args:
        inp_size (int): Input dimension for the model.
        output_path (str, optional): Path where the ONNX model will be saved.
            Defaults to "pk.onnx".
    
    Returns:
        str: Path to the saved ONNX file.
    """
    model = MarabouFriendlyZero(inp_size)
    dummy_input = torch.randn(1, inp_size)

    torch.onnx.export(
        model,
        dummy_input,
        output_path,
        input_names=['input'],
        output_names=['output'],
        # CRITICAL: Disable constant folding so the zero-multiplication
        # isn't optimized away into a single constant before Marabou sees it.
        do_constant_folding=False
    )

    return output_path


def print_it(ce_values, model_path="pk.onnx"):
    """Load an ONNX model and run inference on counter-example inputs.
    
    Args:
        ce_values (array-like): Counter-example input to test.
        model_path (str, optional): Path to the ONNX model. Defaults to "pk.onnx".
    
    Returns:
        tuple: (input, output) from model inference.
        
    Raises:
        ImportError: If onnxruntime is not installed.
        FileNotFoundError: If the model file does not exist.
    """
    if not HAS_ONNXRUNTIME:
        raise ImportError("onnxruntime is required for print_it(). Install with: pip install onnxruntime")
    
    import numpy as np
    
    ce_values = np.array(ce_values, dtype=np.float32)
    if ce_values.ndim == 1:
        ce_values = ce_values.reshape(1, -1)
    
    session = ort.InferenceSession(model_path)
    input_name = session.get_inputs()[0].name
    output_name = session.get_outputs()[0].name

    result = session.run([output_name], {input_name: ce_values})

    print(f"Counter-example input: {ce_values}")
    print(f"Model output: {result[0]}")
    
    return ce_values, result[0]


def calc_e_diff(ke_val, ka_val, precision=5):
    """Calculate interval arithmetic bounds for pharmacokinetic exponents.
    
    Computes ln(ka/ke) / (ka - ke) and related exp terms using mpmath
    interval arithmetic for rigorous over-approximation.
    
    Args:
        ke_val (float): Elimination rate constant.
        ka_val (float): Absorption rate constant.
        precision (int, optional): Decimal places for interval arithmetic. Defaults to 5.
    
    Returns:
        dict: Dictionary with keys 'time_max', 'term1', 'term2', 'result', 'result_upper'.
        
    Raises:
        ValueError: If ka_val == ke_val (division by zero).
    """
    if ke_val == ka_val:
        raise ValueError("ka_val must not equal ke_val (would cause division by zero)")
    
    # Set precision for mpmath
    mp.dps = precision

    # Convert inputs to intervals
    ka = iv.mpf(ka_val)
    ke = iv.mpf(ke_val)

    # 1. Calculate the shared term: ln(ka/ke) / (ka - ke)
    time_max = iv.log(ka / ke) / (ka - ke)

    # 2. Compute the exponents
    term1 = iv.exp(-ke * time_max)
    term2 = iv.exp(-ka * time_max)

    # 3. Final result
    result_interval = term1 - term2

    # Return the upper bound for a strict over-approximation
    return {
        "time_max": time_max,
        "term1": term1,
        "term2": term2,
        "result": result_interval,
        "result_upper": float(result_interval.b),
    }
