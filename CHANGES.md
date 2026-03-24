Changes
=======


CHANGE: Auto-sync VCL scaler values after training
Branch: feat/jess-suggested-vclScalar
Suggested by: Jess
Files changed: src/drug_verification/training.py, pk.vcl

Problem

pk.vcl contained two hardcoded vectors used to normalise inputs before passing
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

Added update_vcl_scaler(scaler, spec_path) in training.py. This function writes
the fitted scaler values to two IDX files — pk_mean.idx and pk_std.idx — using
idx2numpy. It is called automatically in cmd_train immediately after the scaler
is fitted, before any training or export happens, and prints the new values to
stdout so they are visible in training logs.

pk.vcl was updated to declare meanScalingValues and standardDeviationValues as
@dataset rather than inline literals. Vehicle loads them from the .idx files at
verification time via the -d flags in verify.sh:

    -d meanScalingValues:pk_mean.idx
    -d standardDeviationValues:pk_std.idx

The old inline value lines are retained as comments for reference.

Why IDX files rather than rewriting pk.vcl in-place?

Rewriting a spec file at training time risks corrupting it and makes the spec
non-static. IDX files are a clean separation: the spec declares the shape and
role of the datasets, and the files carry the values. Vehicle's @dataset
mechanism is designed exactly for this pattern.

Why auto-update rather than a comment or warning?

A comment is easy to miss. A runtime warning still requires manual action.
Since the correct values are available programmatically at training time,
automating the update removes the possibility of human error entirely and keeps
the spec and the model in sync by construction.


------------------------------------------------------------------------


CHANGE: D_prev as input feature — attempted and reverted
Branch: feat/jess-suggested-vclScalar
Files changed: src/drug_verification/simulation.py (partial — see below)

Problem

The dosing controller used to generate training targets applies strong temporal
smoothing:

    D_t = 0.7 * D_prev + 0.3 * D_t_raw

The previous dose (D_prev) was not included in the feature vector passed to
the neural network, meaning the network was trying to predict a quantity 70%
determined by a hidden state it could not see. This caused consistently high
error regardless of architecture or training duration.

What was tried

D_prev was added as the 6th input feature. The feature vector became
[C, T, WBC, Age, Weight, D_prev]. All downstream files were updated to match
the new input dimensionality (io.py, cli.py, pk.vcl, training_monitor.ipynb).

Impact

Measured on 50 patients, 50 epochs, identical seed:

                    Without D_prev    With D_prev    Change
    Val MSE         54.15             1.39           down 97.4%
    Val MAE         3.70 mg           0.63 mg        down 83.0%
    Max abs error   61.21 mg          13.58 mg       down 77.8%

Why it was reverted

When verification was run against pk.onnx (the actual trained network, not the
trivial zero-weight model), safeFar and safeNear both fail.

The dose target is D_t = 0.7 * D_prev + 0.3 * D_t_raw. With D_prev as a
feature the network learns to copy D_prev almost directly to its output, which
is why accuracy improves so much. But the verifier checks all combinations in
the input box including 0 <= D_prev <= 1500 independently of C. It can
construct inputs like C=29.5, D_prev=500 where the network outputs ~500mg and
pushes concentration above C_safe. In practice this would never happen — a
patient receiving 500mg doses would already have high concentration — but the
verifier has no knowledge of the PK physics linking D_prev and C.

Without D_prev the network cannot learn dosing history and predicts low noisy
outputs regardless of input. It passes verification not because it is safe but
because it never learns to prescribe high doses. It satisfies the properties by
being inaccurate.

                    With D_prev       Without D_prev
    Val MSE         ~1.4              ~54.15
    Val MAE         ~0.63 mg          ~3.70 mg
    Max abs error   ~13 mg            ~61.21 mg
    safeFar         FAIL              PASS
    safeNear        FAIL              PASS
    nonNeg          PASS (clamp)      PASS

Current state

D_prev is used internally in simulate_patient for the dose smoothing
calculation but is not included in the training feature vector. The feature
vector remains [C, T, WBC, Age, Weight] (5 inputs). pk.vcl remains
Tensor Real [5].

nonNeg fix — positive clamp

The output ReLU can saturate to exactly 0 for some inputs, violating the
strict nonNeg output >= 0 requirement in the verifier. A constant +0.0001 Add
node is appended to the ONNX graph inside export_onnx() so that Marabou sees
the clamp as part of the network during verification. pk.vcl was updated from
strict (0 <) to non-strict (0 <=) to match.

Directions to fix safeFar and safeNear with D_prev

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


------------------------------------------------------------------------


Environment

    Python:           3.13.12
    Virtual env:      venv313 (Python 3.13)
    vehicle-lang:     0.24.0
    tensorflow:       2.21.0
    torch:            2.10.0
    scikit-learn:     1.8.0
    onnxruntime:      1.24.3

Setup

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
    bash verify.sh pk.onnx
