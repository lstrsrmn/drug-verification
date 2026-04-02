PDT-Training (Maybe?)
=======

CHANGE: Property driven training and formal verification of safeFar + safeNear
Branch: jess-claude-trial
Files changed: src/drug_verification/training.py, src/drug_verification/vehicle_loss.py,
               src/drug_verification/cli.py, src/drug_verification/constants.py

Background

The goal here was to train a network that is both accurate and formally verified against 
the two safety properties:

- `safeFar`  — when current concentration is well below C_safe, the predicted dose should not push concentration above C_safe.
- `safeNear` — when current concentration is near C_safe (within 1%), the predicted dose must be near-zero (< eps = 0.001 mg).

------------------------------------------------------------------------
To Run:
I have 2 different venv/ to handle the package conflicts

1: With your training venv:
```bash
pk train --vehicle-loss --phase-switch 20 --alpha 0.3 --epochs 100 --save-model models/pk_model.keras
pk export --model-path models/pk_model.keras --onnx-out models/pk.onnx
```

2: With your verification venv:
```bash
./verify.sh models/pk.onnx
```

------------------------------------------------------------------------

FIX: Scaler std floor to prevent NaN in Vehicle normalisation
File: src/drug_verification/training.py (prepare_data)

Problem

With KE=3.5 and 12-hour dosing intervals, trough concentrations between doses
are effectively zero for all patients:

```
e^(-3.5 * 12) ≈ 1.5e-18
```

Because all training samples had concentration ≈ 0, the StandardScaler fitted
a near-zero standard deviation for that feature (scale_ ≈ 1e-15). The Vehicle
spec's normalise function then computed:

```
(conc - mean) / scale_ = (15 - 0) / 1e-15 = 1e16
```

which overflows to NaN inside the network's first Dense layer, causing all
constraint loss values and gradients to be NaN throughout training.

Fix

After fitting the scaler, floor each element of scale_ to 1e-2:

```python
scaler.scale_ = np.maximum(scaler.scale_, 1e-2)
```

This caps the normalised concentration at 15 / 0.01 = 1500 — large but
finite, so gradients flow normally. The floor only activates when a feature
has very low variance in the training data; for temperature, WBC, age, and
weight the fitted std is well above 0.01 and is unchanged.

The fix also applies to the generated training spec (vehicle_loss.py
generate_training_spec), which inlines the same scaler values as literals.

------------------------------------------------------------------------

FIX: Output layer changed from ReLU to linear; ReLU moved to ONNX export
File: src/drug_verification/training.py (build_model, export_onnx)

Problem

The final Dense layer previously used `activation="relu"`. When ReLU saturates
(output exactly 0), gradient flow to earlier layers is cut during the
constraint training phase, slowing or stalling learning. Additionally, the
previous ONNX export only added a +0.0001 Add node without an explicit ReLU,
meaning the exported model could theoretically output negative values for some
inputs (violating the nonNeg property).

Fix

Changed the Keras model's output activation to `"linear"` so that gradients
always flow during training. The non-negativity clamp is now applied in two
steps at ONNX export time:

1. A Relu node is appended to the graph to clamp negatives to zero.
2. A +0.0001 Add node is appended after the Relu to shift the output strictly above zero.

The exported model therefore satisfies output > 0 by construction, and the
Keras model trains with unrestricted gradients.

------------------------------------------------------------------------

CHANGE: Two-phase constraint training (phase_switch)
File: src/drug_verification/training.py (train_model_with_constraint)
      src/drug_verification/cli.py (add_train_args)

Motivation

Switching on constraint loss from epoch 1 with a randomly initialised network
produced very large initial constraint gradients (magnitude ~14000 at epoch 21)
that overwhelmed the task loss signal. The network converged to a degenerate
state — constraint satisfied but predictions near-zero, which is safe but
clinically meaningless.

Training pattern

A two-phase schedule was added via the `--phase-switch` flag:

- Phase 1 (epochs 1–N): train on task loss only (MSE). The network learns to predict clinically reasonable doses before constraints are introduced.
- Phase 2 (epochs N+1–end): switch on constraint loss alongside task loss. The network already has a reasonable starting point so constraint gradients refine rather than dominate.

The verified run used `--phase-switch 20` with 100 total epochs and `alpha=0.3`
(meaning 30% task loss, 70% constraint loss in phase 2).

Implementation

```python
constraint_active = (phase_switch == 0) or (epoch >= phase_switch)
```

When `constraint_active` is False, `constraint_loss` is set to zero and `total_loss`
equals `task_loss` only. The Adam optimiser accumulates useful task gradient
history during phase 1, which is preserved when phase 2 begins.

The `--normalise-losses` flag (experiment 1, not used in the verified run) was
also added: it divides both losses by their first-batch values so alpha is
scale-independent. This did not improve results compared to the phase-switch
approach and was not used in the final verified model.

------------------------------------------------------------------------

CHANGE: safeFar generated spec with inlined parameters
File: src/drug_verification/vehicle_loss.py (generate_training_spec)

Problem

Vehicle's loss compiler collapsed the `if Ka < Ke` branch in pk.vcl to a
constant when Ka and Ke were `@parameter` declarations, returning a flat loss
that provided no gradient signal.

Fix

`generate_training_spec()` produces a minimal temporary .vcl that inlines Ka,
Ke, Vd, and the scaler values as literals, and resolves the if/else branch at
generation time. The file is written to a NamedTemporaryFile, compiled, and
immediately deleted. safeNear continues to load directly from pk.vcl because
Vehicle 0.24.1 resolves `@parameter` declarations correctly for that property.

------------------------------------------------------------------------

RESULT: Formal verification — safeFar and safeNear both proven
Tool: Vehicle 0.24.1 + Marabou
Date: 2026-04-02

Both safety properties were formally verified against the exported ONNX model.

Result: No counterexample found for either property. Marabou exhaustively
searched the input domain and proved the properties hold.

| Property | Input region                        | Result   |
|----------|-------------------------------------|----------|
| safeFar  | conc in [0, 29.7], vitals in range  | VERIFIED |
| safeNear | conc in [29.7, 30], vitals in range | VERIFIED |
| nonNeg   | conc in [0, 30], vitals in range    | VERIFIED |

Why the constraint loss dropped to 0 so fast (the suspicious...)

The phase-2 constraint gradient at epoch 21 had magnitude ~14145 — a very
strong signal that shoved the model into a safe region in one large step.
After that, the task loss kept it there: with near-zero trough concentrations
(`e^(-3.5*12) ≈ 0`) the network naturally learns to predict conservative doses,
which happen to satisfy the safety constraints. The constraint loss reaching 0
after a single epoch in phase 2:

Accuracy at time of verification

| Metric             | Value          |
|--------------------|----------------|
| Test MAE           | 7.4 mg         |
| Test MSE           | see training log |
| Max absolute error | 260 mg         |

The 260 mg maximum error is the main open clinical question. The network is
formally safe — no input in the verified domain produces an unsafe dose — but
whether predictions are clinically accurate for fast-elimination patients
(high effective Ke after age covariate adjustment) is a separate concern.
Verification passing means no patient is overdosed; it does not guarantee
the dose is the most therapeutically effective one.

------------------------------------------------------------------------

Clinical Relevance:
`drug-verification/clinical_relevance.ipynb`

The concern is that a model could pass verification by being pathologically conservative — always predicting near-zero doses 
regardless of how sick the patient is. That satisfies safeFar and safeNear trivially (undertreated patients).

The model is clinically relevant. It is not the degenerate case — it is not a flat conservative predictor that passes verification 
by prescribing near-zero doses. It accurately tracks the clinical state of the patient and scales doses appropriately. The formal 
verification result is meaningful, not hollow.

Does the model prescribe different doses for different patients, or has constraint training flattened it?
The model correctly prescribes ~3.5× higher doses for high-fever, high-WBC patients compared to near-normal patients. The standard deviation 
of predictions (114.1 mg) is essentially identical to the true dose distribution (114.3 mg), and the overall correlation is r = 0.989. 
This is not a flat predictor. (yay)

The 260 mg max error is a first-dose artefact. Every single one of the top 10 worst errors shares the same signature:
- Timestep 0 or 1 — the very start of treatment
- Concentration = 0.00 — no drug on board
- Residual is always negative — the model underestimates the first dose

What is happening: at timestep 0 the patient is maximally sick (fever 38.5–39°C, WBC 12–16) with zero drug concentration. The dosing controller prescribes a large loading dose (~370–415 mg). The model predicts something lower (~110–290 mg). After the first dose, concentration rises above zero, and the model's subsequent predictions are very accurate — the same patient (33) who drives the 260 mg worst case has a per-patient MAE of only 16.8 mg across all 47 timesteps. 

This is an underdosing error at the start of treatment, not an overdosing error. The clinical consequence is that a patient would receive a lower-than-optimal first dose — suboptimal, but not a safety violation. All formal safety properties hold.

For 98.3% of predictions the model is within 50 mg of the target. That is clinically reasonable for a dosing support tool. There is no systematic over- or under-dosing bias.

One structural concern: the verified region is never visited in practice

With Ke = 3.5 hr⁻¹ and 12-hour dosing intervals, trough concentration is effectively 0 for all patients — every single training sample has concentration in [0, 5) mg/L. The verification covers safeFar (conc ∈ [0, 29.7]) and safeNear (conc ∈ [29.7, 30]), but the model has never seen a patient with concentration above ~5 mg/L. 

This means the safety properties are verified against a region the model has no training data for. Marabou proved it holds, but it holds over inputs the network is effectively extrapolating on. If the simulation parameters were changed to produce sustained concentrations (lower Ke, shorter dosing intervals, or an accumulation scenario), the clinical accuracy in that region is unknown — even though formal safety is guaranteed. 

------------------------------------------------------------------------
