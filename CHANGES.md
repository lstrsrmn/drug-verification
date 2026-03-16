# Changes


## feat/jess-suggested-vclScalar — Auto-sync VCL scaler values after training

**Suggested by:** Jess
**Branch:** `feat/jess-suggested-vclScalar`
**Files changed:** `src/drug_verification/training.py`, `src/drug_verification/cli.py`, `pk.vcl`

### Problem

`pk.vcl` contains two hardcoded vectors used to normalise inputs before passing
them to the network during formal verification:

```
meanScalingValues        = [...]
standardDeviationValues  = [...]
```

These must exactly match the `StandardScaler` fitted during training. However,
they were previously static — retraining with different data (different
`--num-patients`, `--timesteps`, or `--seed`) produces a new scaler, but the
spec was never updated. This means the verified property could apply to a
*different* normalisation than the exported ONNX model actually uses,
**silently invalidating the formal proof** without any error or warning.

### Fix

Added `update_vcl_scaler(scaler, spec_path)` in `training.py`. This function:

- Uses regex to rewrite only the two value lines in `pk.vcl` in-place.
- Is called automatically in `cmd_train` (in `cli.py`) immediately after the
  scaler is fitted, before any training or export happens.
- Prints the new values to stdout so they are visible in training logs.

A warning comment was also added above the two lines in `pk.vcl` to make clear
they are auto-generated and should not be edited by hand.

### Why auto-update rather than a comment or warning?

A comment is easy to miss. A runtime warning still requires manual action. Since
the correct values are available programmatically at training time, automating
the update removes the possibility of human error entirely and keeps the spec
and the model in sync by construction.

---

## feat/jess-suggested-vclScalar — Add D_prev as input feature

**Branch:** `feat/jess-suggested-vclScalar`
**Files changed:** `src/drug_verification/simulation.py`, `src/drug_verification/io.py`, `src/drug_verification/cli.py`, `pk.vcl`, `training_monitor.ipynb`

### Problem

The dosing controller used to generate training targets applies strong temporal
smoothing:

```python
D_t = 0.7 * D_prev + 0.3 * D_t_raw
```

The previous dose (`D_prev`) was not included in the feature vector passed to
the neural network, meaning the network was trying to predict a quantity 70%
determined by a hidden state it could not see. This caused consistently high
error regardless of architecture or training duration.

### Fix

Added `D_prev` as the 6th input feature in `simulate_patient` (index 5).
The feature vector is now `[C, T, WBC, Age, Weight, D_prev]`.

Updated all downstream files to match the new input dimensionality:

- `io.py` — column header list extended to include `D_prev`
- `cli.py` — `pk test --input-size` default updated from 5 to 6
- `pk.vcl` — input tensor type updated from `Tensor Real [5]` to `Tensor Real [6]`,
  `dprev = 5` index added, scaler arrays extended (updated by `pk train`),
  and `0 <= x ! dprev <= 1500` bounds added to `safeFarInput`, `safeNearInput`,
  and `safeInput`
- `training_monitor.ipynb` — `feature_names` and residuals subplot updated

### Impact

Measured on 50 patients, 50 epochs, identical seed:

| Metric | Without D_prev | With D_prev | Change |
|---|---|---|---|
| Val MSE | 54.15 | 1.39 | ↓ 97.4% |
| Val MAE | 3.70 mg | 0.63 mg | ↓ 83.0% |
| Max absolute error | 61.21 mg | 13.58 mg | ↓ 77.8% |

Formal verification with Vehicle + Marabou confirmed all 9 properties in
`pk.vcl` still hold against the rebuilt `marabou_zero.onnx` (6-input) model.
