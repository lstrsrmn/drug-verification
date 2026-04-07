PDT-Training — GradNorm Automated Constraint Balancing
=======

COMPARISON: trial/pdt-training (this branch) vs trial/manual-pdt-training
------------------------------------------------------------------------

Both branches share the same goal — train a formally verified PK dosing network —
and both verified all properties. The core difference is how the three losses
(task, safeFar, safeNear) are balanced during phase 2.

Approach
  manual-pdt-training:  fixed alpha — `--alpha 0.3` splits weight 30% task /
                        70% constraint, fixed for all of phase 2.
  pdt-training (this):  GradNorm — weights adapt each batch based on per-loss
                        gradient norms and training-rate ratios.

Loss scale mismatch problem
  manual-pdt-training:  not addressed. Task MSE was on raw doses (~25,000 mg²)
                        vs constraint losses (~1.0), but fixed alpha masked this
                        by heavily weighting constraints.
  pdt-training (this):  fixed by (a) y-normalisation — model trains in
                        normalised dose space, scaler inverse-transforms for
                        evaluation and constraint functions; and (b) normalising
                        per-loss gradients by initial values inside GradNorm so
                        all three losses start at ~1.0.

Gradient instability at phase_switch
  manual-pdt-training:  not addressed. Constraint gradient magnitude ~14,000 at
                        epoch 21 caused a single large weight update that landed
                        in a safe region. Worked, but relied on that one-step
                        jump.
  pdt-training (this):  Adam optimiser reset with `clipnorm=1.0` at phase_switch
                        prevents the Adam second-moment estimates from the
                        task-only phase from producing outsized steps when
                        constraint gradients arrive.

Tape gradient path
  manual-pdt-training:  not an issue (single total_loss, standard tape).
  pdt-training (this):  `tape.gradient(total_loss, ...)` returned zeros because
                        the weighted sum was assembled outside the tape context.
                        Fixed by computing per-loss gradients individually and
                        combining manually with GradNorm weights.

Shared fixes (ported from manual-pdt-training into this branch)
  - Scaler std floor (scale_ >= 1e-2) to prevent NaN in Vehicle normalisation
  - Output layer linear in Keras; ReLU + Add(0.0001) appended at ONNX export
  - Two-phase training via --phase-switch flag
  - safeFar generated spec with inlined PK parameters (Vehicle branch collapse bug)

Results comparison

  | Metric                  | manual-pdt-training | pdt-training (this) |
  |-------------------------|---------------------|---------------------|
  | Test MAE                | 7.4 mg              | 4.8 mg              |
  | Max absolute error      | 260 mg              | 146 mg              |
  | Corr(true, pred)        | 0.989               | 0.996               |
  | Pred std / True std     | ~1.00               | 1.030               |
  | High-temp dose ratio    | ~3.5x               | 4.45x               |
  | safeFar verified        | yes                 | yes                 |
  | safeNear verified       | yes                 | yes                 |
  | nonNeg verified         | yes                 | yes                 |

GradNorm improved accuracy (MAE -35%, max error -44%) while preserving
verification. Both worst-case error patterns are the same: underdosing at
timestep 0–1 for high-severity patients with zero initial concentration.

=======

CHANGE: Property-driven training with GradNorm adaptive loss balancing
Branch: trial/pdt-training
Files changed: src/drug_verification/grad_norm.py (new),
               src/drug_verification/tuning.py (new),
               src/drug_verification/training.py,
               src/drug_verification/vehicle_loss.py,
               src/drug_verification/cli.py,
               src/drug_verification/constants.py

Background

The goal here was to train a network that is both accurate and formally verified against
the two safety properties, using GradNorm to automatically balance the three losses rather
than the manual phase_switch + fixed alpha approach in trial/manual-pdt-training:

- `safeFar`  — when current concentration is well below C_safe, the predicted dose should not push concentration above C_safe.
- `safeNear` — when current concentration is near C_safe (within 1%), the predicted dose must be near-zero (< eps = 0.001 mg).

------------------------------------------------------------------------
To Run:
I have 2 different venv/ to handle the package conflicts

1: With your training venv:
```bash
pk train --vehicle-loss --phase-switch 20 --epochs 100 --save-model models/pk_model.keras
pk export --model-path models/pk_model.keras --onnx-out models/pk.onnx
```

2: With your verification venv:
```bash
./verify.sh models/pk.onnx
```

------------------------------------------------------------------------

FIX: Scaler std floor to prevent NaN in Vehicle normalisation
File: src/drug_verification/training.py (prepare_data)

Ported from trial/manual-pdt-training. With KE=3.5 and 12-hour dosing intervals,
trough concentrations are effectively zero for all patients:

```
e^(-3.5 * 12) ≈ 1.5e-18
```

This caused the StandardScaler to fit a near-zero std for concentration (scale_ ≈ 1e-15).
The Vehicle spec normalisation then computed:

```
(conc - mean) / scale_ = (15 - 0) / 1e-15 = 1e16
```

which overflowed to NaN inside the network, making all constraint losses and gradients NaN.

Fix: floor each element of `scale_` to `1e-2` after fitting:

```python
scaler.scale_ = np.maximum(scaler.scale_, 1e-2)
```

------------------------------------------------------------------------

CHANGE: y-target normalisation
File: src/drug_verification/training.py (prepare_data, train_model_with_constraint)

The task loss MSE on raw doses (~25,000 mg²) was four orders of magnitude larger than
the Vehicle constraint losses (~1.0). This caused GradNorm to immediately collapse the
task weight toward zero.

Fix: `prepare_data` now also fits a `StandardScaler` on `y_train` and returns a `y_scaler`.
The model is trained in normalised dose space. `train_model_with_constraint` receives
`y_mean` and `y_std` and wraps `network_fn` to de-normalise output before passing to
Vehicle constraint functions, which expect doses in physical units (mg):

```python
def network_fn(x):
    normalised = model(tf.reshape(x, [1, -1]), training=True)
    return normalised * y_std + y_mean
```

`evaluate_model` accepts an optional `y_scaler` and inverse-transforms predictions
before computing metrics so reported errors are in mg.

The y scaler values are saved to `data/pk_y_mean.idx` and `data/pk_y_std.idx`.

------------------------------------------------------------------------

CHANGE: GradNorm adaptive loss balancing
File: src/drug_verification/grad_norm.py (new)

GradNorm (Chen et al., ICML 2018) adapts per-task loss weights online so that each loss
trains at a similar rate. The three losses are:

- `task`     — MSE between predicted and target dose
- `safeFar`  — Vehicle-compiled loss for the safeFar property
- `safeNear` — Vehicle-compiled loss for the safeNear property

`GradNorm` maintains a `tf.Variable` weight vector updated each batch using a separate
Adam optimiser. Weights are projected to sum to `n_tasks=3` and floored at `min_weight`
to prevent any task from being zeroed out.

GradNorm computes:

```python
inverse_train_rate = (loss / initial_loss) / mean(loss / initial_loss)
target_norm = mean_grad_norm * inverse_train_rate ^ alpha
grad_norm_loss = sum(|weight * grad_norm - target_norm|)
```

Harder tasks (high loss ratio) receive higher target gradient norms → higher weights.

------------------------------------------------------------------------

FIX: Manual gradient combination to unblock frozen model weights
File: src/drug_verification/grad_norm.py (balance)

Problem: the model weights were completely frozen after phase 2 started. Constraint losses
were identical to 4 decimal places for 10+ epochs. Root cause: `tape.gradient(total_loss, model_variables)`
was returning zero/None gradients because `total_loss` was assembled from stacked losses
outside the tape context, breaking TF's gradient path.

Fix: bypass `tape.gradient(total_loss, ...)` entirely. Instead, compute per-loss gradients
individually via the tape (which works correctly), then manually combine with GradNorm weights:

```python
g_task       = tape.gradient(task_loss,        model_variables)
g_constraint = tape.gradient(constraint_loss,  model_variables)
g_constraint2= tape.gradient(constraint2_loss, model_variables)

model_grad = w0 * g_task / initial_task + w1 * g_con / initial_con + w2 * g_con2 / initial_con2
```

This is mathematically equivalent to differentiating the normalised weighted total loss, but
avoids the gradient path breakage entirely.

------------------------------------------------------------------------

FIX: Loss normalisation by initial values
File: src/drug_verification/grad_norm.py (balance)

Problem: at phase 2 epoch 1, safeFar ≈ 46.8 and safeNear ≈ 1105.9, versus task ≈ 0.013.
Gradient norms from safeNear were ~88,000× larger than task. GradNorm tried to equalise
by reducing safeNear weight, but hit the `min_weight` floor before achieving balance.

Fix: each loss is divided by its initial value (captured at the first `balance` call) before
computing the weighted combination and `base_norms` for GradNorm's weight update:

```python
normalised_losses = losses / (initial_losses + eps)
```

All three losses now start at ~1.0, so gradient norms are comparable and GradNorm can
balance meaningfully from the first epoch of phase 2.

------------------------------------------------------------------------

FIX: Adam optimizer reset at phase_switch
File: src/drug_verification/training.py (train_model_with_constraint)

Problem: Adam accumulated second moment estimates (v) during 20 epochs of task-only
training calibrated to small task gradients. When constraint gradients (~1000× larger)
arrived at epoch 21, Adam's effective step size = lr / sqrt(v + eps) was enormous,
causing overshooting and instability.

Fix: at `epoch == phase_switch`, replace the optimizer with a fresh Adam instance with `clipnorm=1.0`:

```python
if phase_switch > 0 and epoch == phase_switch:
    optimizer = tf.keras.optimizers.Adam(learning_rate=optimizer_lr, clipnorm=1.0)
```

------------------------------------------------------------------------

FIX: min_weight floor lowered from 0.2 to 0.05
File: src/drug_verification/grad_norm.py, src/drug_verification/constants.py

With the previous 0.2 floor, GradNorm hit the minimum weight for safeNear after only a
few epochs and stopped rebalancing. The model gradients were then dominated by whatever
remained at the floor. Lowered to 0.05 to give GradNorm more room to balance freely.

------------------------------------------------------------------------

CHANGE: Two-phase constraint training (phase_switch)
File: src/drug_verification/training.py, src/drug_verification/cli.py

Same motivation as trial/manual-pdt-training. Switching on GradNorm constraint balancing
from epoch 1 with a randomly initialised network overwhelms the task loss signal.

A `--phase-switch` flag trains on task loss only for N epochs, then activates GradNorm:

- Phase 1 (epochs 1–N): task loss only — model learns clinically reasonable doses first.
- Phase 2 (epochs N+1–end): GradNorm balances task + safeFar + safeNear.

The verified run used `--phase-switch 20` with 100 total epochs.

------------------------------------------------------------------------

RESULT: Formal verification — PASSED
Tool: Vehicle 0.24.1 + Marabou

```
Verifying properties:
  Ka_pos    [..] 0/0 queries  result: 🗸 - (trivial)
  Ke_pos    [..] 0/0 queries  result: 🗸 - (trivial)
  Ke_n_Ka   [..] 0/0 queries  result: 🗸 - (trivial)
  Vd_pos    [..] 0/0 queries  result: 🗸 - (trivial)
  C_safe_pos[..] 0/0 queries  result: 🗸 - (trivial)
  ttd_pos   [..] 0/0 queries  result: 🗸 - (trivial)
  safeFar   [==] 1/1 queries  result: 🗸 - Marabou proved no counterexample exists
  safeNear  [==] 1/1 queries  result: 🗸 - Marabou proved no counterexample exists
  nonNeg    [==] 1/1 queries  result: 🗸 - Marabou proved no counterexample exists
```

All 9 properties verified. The 6 trivial properties are structural bounds on
the PK parameters (Ka, Ke, Vd, C_safe, ttd all positive; Ke < Ka). The three
non-trivial properties required Marabou to search for counterexamples and found
none.

------------------------------------------------------------------------

RESULT: Clinical relevance — PASSED
File: clinical_relevance.ipynb

The concern is that a model could pass verification by being pathologically
conservative — predicting near-zero doses regardless of patient state. The
notebook confirms this is not the case.

Summary (50 patients, 2350 samples):

  MAE                        4.8 mg
  95th percentile error     19.5 mg
  99th percentile error     37.3 mg
  Max absolute error       146.0 mg   (underdose at timestep 0, high-severity patient)
  Mean bias                 +0.9 mg   (slight overdosing on average)
  Within 50 mg             99.6%
  Within 100 mg            99.9%

  Pred std / True std       1.030     (1.0 = perfectly responsive)
  Corr(true, pred)          0.996

  Low temp dose:   58.3 mg
  High temp dose: 259.5 mg            (4.45x ratio — model responds to severity)

Model is clinically responsive (r = 0.996) and prediction variance matches true
dose variance — not a flat conservative predictor. Worst-case errors are
underdoses at early timesteps for high-severity patients (high fever + WBC),
which is suboptimal but not a safety violation.

------------------------------------------------------------------------
