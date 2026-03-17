Changes
=======


CHANGE: Auto-sync VCL scaler values after training
Branch: feat/jess-suggested-vclScalar
Suggested by: Jess
Files changed: src/drug_verification/training.py, src/drug_verification/cli.py, pk.vcl

Problem

pk.vcl contains two hardcoded vectors used to normalise inputs before passing
them to the network during formal verification:

    meanScalingValues        = [...]
    standardDeviationValues  = [...]

These must exactly match the StandardScaler fitted during training. However,
they were previously static. Retraining with different data (different
--num-patients, --timesteps, or --seed) produces a new scaler, but the spec
was never updated. This means the verified property could apply to a different
normalisation than the exported ONNX model actually uses, silently invalidating
the formal proof without any error or warning.

Fix

Added update_vcl_scaler(scaler, spec_path) in training.py. This function uses
regex to rewrite only the two value lines in pk.vcl in-place. It is called
automatically in cmd_train (in cli.py) immediately after the scaler is fitted,
before any training or export happens, and prints the new values to stdout so
they are visible in training logs.

A warning comment was also added above the two lines in pk.vcl to make clear
they are auto-generated and should not be edited by hand.

Why auto-update rather than a comment or warning?

A comment is easy to miss. A runtime warning still requires manual action.
Since the correct values are available programmatically at training time,
automating the update removes the possibility of human error entirely and keeps
the spec and the model in sync by construction.


------------------------------------------------------------------------


CHANGE: Add D_prev as input feature
Branch: feat/jess-suggested-vclScalar
Files changed: src/drug_verification/simulation.py, src/drug_verification/io.py,
               src/drug_verification/cli.py, pk.vcl, training_monitor.ipynb

Problem

The dosing controller used to generate training targets applies strong temporal
smoothing:

    D_t = 0.7 * D_prev + 0.3 * D_t_raw

The previous dose (D_prev) was not included in the feature vector passed to
the neural network, meaning the network was trying to predict a quantity 70%
determined by a hidden state it could not see. This caused consistently high
error regardless of architecture or training duration.

Fix

Added D_prev as the 6th input feature in simulate_patient (index 5).
The feature vector is now [C, T, WBC, Age, Weight, D_prev].

Updated all downstream files to match the new input dimensionality:

    io.py              column header list extended to include D_prev
    cli.py             pk test --input-size default updated from 5 to 6
    pk.vcl             input tensor type updated from Tensor Real [5] to
                       Tensor Real [6], dprev = 5 index added, scaler arrays
                       extended (updated by pk train), and bounds
                       0 <= x ! dprev <= 1500 added to safeFarInput,
                       safeNearInput, and safeInput
    training_monitor.ipynb    feature_names and residuals subplot updated

Impact

Measured on 50 patients, 50 epochs, identical seed:

                    Without D_prev    With D_prev    Change
    Val MSE         54.15             1.39           down 97.4%
    Val MAE         3.70 mg           0.63 mg        down 83.0%
    Max abs error   61.21 mg          13.58 mg       down 77.8%

Formal verification with Vehicle + Marabou confirmed all 9 properties in
pk.vcl still hold against the rebuilt marabou_zero.onnx (6-input) model.

Verification findings — D_prev and the accuracy/verifiability tension

When verification was run against pk.onnx (the actual trained network, not the
trivial zero-weight model), safeFar and safeNear both fail. nonNeg passes after
a +0.0001 clamp was added to the ONNX graph at export.

Why D_prev causes safeFar and safeNear to fail:

The dose target is D_t = 0.7 * D_prev + 0.3 * D_t_raw. With D_prev as a
feature the network learns to copy D_prev almost directly to its output, which
is why accuracy improves so much. But the verifier checks all combinations in
the input box including 0 <= D_prev <= 1500 independently of C. It can
construct inputs like C=29.5, D_prev=500 where the network outputs ~500mg and
pushes concentration above C_safe. In practice this would never happen — a
patient receiving 500mg doses would already have high concentration — but the
verifier has no knowledge of the PK physics linking D_prev and C.

Why removing D_prev passes verification:

Without D_prev the network cannot learn dosing history and predicts low noisy
outputs regardless of input. It passes verification not because it is safe but
because it never learns to prescribe high doses. It satisfies the properties by
being inaccurate.

                    With D_prev       Without D_prev
    Val MSE         ~1.4              ~14,055
    Val MAE         ~0.63 mg          ~52.96 mg
    Max abs error   ~13 mg            ~482 mg
    safeFar         FAIL              PASS
    safeNear        FAIL              PASS
    nonNeg          PASS (clamp)      PASS

nonNeg fix — positive clamp:

The output ReLU can saturate to exactly 0 for some inputs, violating the
strict output > 0 requirement. A constant +0.0001 Add node is appended to the
ONNX graph inside export_onnx() so that Marabou sees the clamp as part of the
network during verification.

Directions to fix safeFar and safeNear:

1. Tighten D_prev bounds in the spec — add a joint constraint between D_prev
   and C reflecting PK physics so the verifier only checks physically reachable
   inputs.

2. Vehicle-loss training — use train_model_with_constraint (already in the
   codebase) to penalise violations of safeNear during training, teaching the
   network to suppress doses when C is near C_safe even when D_prev is high.

3. Architectural safety layer — multiply the output by
   max(0, (C_safe - C) / C_safe) so that as C approaches C_safe the output is
   forced toward zero by construction, making safeNear trivially provable
   regardless of what the network learned.

Environment

    Python:           3.13.12
    Virtual env:      venv313 (Python 3.13)
    vehicle-lang:     0.24.0
    tensorflow:       2.21.0
    torch:            2.10.0
    scikit-learn:     1.8.0
    onnxruntime:      1.24.3

Setup:

    python3.13 -m venv venv313
    source venv313/bin/activate
    pip install -e .

Commands

Train:

    source venv313/bin/activate
    pk train --save-model pk_model.keras
    pk export --model-path pk_model.keras --onnx-out pk.onnx

Verify:

    source venv313/bin/activate
    vehicle verify -v Marabou -s pk.vcl -n pk:pk.onnx -c cache \
      -p Ka:4.5 -p Ke:3.5 -p Vd:10 -p C_safe:30 -p ttd:2 \
      -p Ka_over:0.3228 -p Ka_under:0.3227 \
      -p Ke_over:0.415 -p Ke_under:0.4149 \
      -p eps:0.001
