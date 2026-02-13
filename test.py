import onnxruntime as ort
import numpy as np
import torch
import torch.nn as nn
from mpmath import mp, iv

def print_it():
    # 1. Load the model
    session = ort.InferenceSession("marabou_zero.onnx")

    # ce_values = np.array([[29.9999, 36.5, 7.5, 18, 50, 0][:2]], dtype=np.float32)

    input_name = session.get_inputs()[0].name
    output_name = session.get_outputs()[0].name

    result = session.run([output_name], {input_name: ce_values})

    print(f"Counter-example input: {ce_values}")
    print(f"Model output: {result[0]}")


class MarabouFriendlyZero(nn.Module):
    def __init__(self, inp_size):
        super().__init__()
        # We use a Linear layer with weights and bias initialized to 0
        self.fc = nn.Linear(inp_size, 1)
        nn.init.constant_(self.fc.weight, 0)
        nn.init.constant_(self.fc.bias, 0.0001)

    def forward(self, x):
        return self.fc(x)

def build_it(inp_size):
    model = MarabouFriendlyZero(inp_size)
    dummy_input = torch.randn(1, inp_size)

    torch.onnx.export(
        model,
        dummy_input,
        "marabou_zero.onnx",
        input_names=['input'],
        output_names=['output'],
        # CRITICAL: Disable constant folding so the zero-multiplication
        # isn't optimized away into a single constant before Marabou sees it.
        do_constant_folding=False
    )

    print("Connected model saved for Marabou.")

mp.dps = 5

def calc_e_diff(ke_val, ka_val):
# Convert inputs to intervals
    ka = iv.mpf(ka_val)
    ke = iv.mpf(ke_val)

    # 1. Calculate the shared term: ln(ka/ke) / (ka - ke)
    # Interval arithmetic handles the rounding automatically
    time_max = iv.log(ka / ke) / (ka - ke)

    # 2. Compute the exponents
    term1 = iv.exp(-ke * time_max)
    term2 = iv.exp(-ka * time_max)

    # 3. Final result
    result_interval = term1 - term2

    # Return the upper bound for a strict over-approximation
    print(f"Over approx: {float(result_interval.b)}")

build_it(5)
# print_it()
# calc_e_diff(3.5, 4.5)
