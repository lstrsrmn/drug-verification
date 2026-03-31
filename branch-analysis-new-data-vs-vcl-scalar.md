# Branch Analysis: `new-data` vs `feat/jess-suggested-vclScalar`

## Overview

This document details every change introduced in `new-data` relative to
`feat/jess-suggested-vclScalar`, the impact each change has on the training
pipeline, and the downstream consequences for formal verification via Vehicle.

---

## 1. PK Model: Euler → Oral Absorption (Superposition)

**Files:** `simulation.py`, `constants.py`, `types.py`

### What changed

The previous branch used a single-step Euler approximation for drug concentration:

```python
# vcl-scalar
C_next = conc + dt * (-ke_eff * conc + D_t / Vd_eff)   # dt = 0.5 h
C_next = max(0, C_next)
```

`new-data` replaces this with the closed-form one-compartment oral absorption
equation, accumulated over all prior doses via superposition:

```python
# new-data
curve = lambda d: lambda t: max(0,
    (d * ka_eff) / (Vd_eff * (ka_eff - ke_eff))
    * (exp(-ke_eff * t) - exp(-ka_eff * t))
)
C_next = sum(curve(ds[j])(i * ttd + T_peak - j * ttd)
             for j in range(i + 1))
# where T_peak = ln(ka_eff / ke_eff) / (ka_eff - ke_eff)
```

Doses are given every `ttd = 12` hours; `DT` is also set to 12 in `constants.py`.
`ka` (0.2 /h) is added to `SimulationConfig` and `EffectiveParams`, with an
age-based adjustment mirroring the existing `ke` adjustment.

### Training impact

| Aspect | Effect |
|--------|--------|
| **More realistic PK** | The training data now reflects genuine oral bioavailability dynamics (lag, rise to peak, exponential decline). The model learns to dose against a more physically correct trajectory. |
| **C_next is peak concentration** | The value stored as `conc` at each step is evaluated at `T_peak` of the *current* dose, not at the end of the 12-hour interval. The PD dynamics (temperature, WBC) still use `dt=12` and the same `conc` value. This is inconsistent: PD effects see peak-drug concentration rather than an average or trough. |
| **Superposition grows unboundedly** | Every previous dose contributes to `C_next` with no cutoff. Over 47 timesteps (~23 days) the number of terms grows linearly. Early doses decay exponentially but never reach zero, so the sum is always slightly inflated. For long simulations with high doses this can push `C_next` unrealistically high, skewing the dose targets the model is trained on. |
| **`conc` feature inconsistency** | The feature vector appended *before* the Euler update was the true `conc` from the previous step. In the new code the update still follows that pattern, but the updated `conc` passed to the next T/WBC step is the *peak* of this step—not the concentration the patient actually has when the next dose decision is made. The model therefore learns a mapping where the `conc` input does not match the concentration regime used to generate the label. |

### Verification impact

The Vehicle spec `safeFar` in `pk.vcl` uses exactly the same oral absorption
formula to define the safety postcondition:

```vehicle
safeFarOutput x = let y = ((((normpk x) ! 0) * Ka) / (Vd * (Ka - Ke))) in
  if Ka < Ke then (x ! conc) + y * (Ke_under - Ka_over) < C_safe
             else (x ! conc) + y * (Ke_over - Ka_under) < C_safe
```

The switch to `safeFar` (see §4) therefore **closes the model–spec gap** that
existed in `vcl-scalar`: both the simulator and the property now agree on what
the next peak concentration will be. This is the most significant *positive*
alignment change in the branch.

However, the inconsistency in how `conc` is computed (peak, not trough) means
that the verified property is over a region of input space where `conc` is
systematically higher than what a real patient would present at the next dosing
time. The set of inputs the verifier explores may not fully cover the
practically reachable states.

---

## 2. Training Loss: Alpha Set to Zero

**File:** `training.py` — `train_model_with_constraint`, line 192

### What changed

```python
# vcl-scalar
alpha = 0.5   # 50 % task loss, 50 % constraint loss

# new-data
alpha = 0.0   # 0 % task loss, 100 % constraint loss
```

With `alpha = 0.0`:

```python
total_loss = 0.0 * task_loss + 1.0 * constraint_loss
```

The MSE against the simulation labels contributes **zero gradient**. The model
is trained solely to satisfy the Vehicle constraint.

### Training impact

- The model receives no signal from the simulation data during
  `train_model_with_constraint`. Weights will drift toward satisfying the
  constraint regardless of whether the resulting doses are clinically sensible.
- If the constraint loss has a trivial minimiser (e.g. always output 0),
  nothing prevents the model from collapsing to it.
- The `task_loss` is still computed and logged, so it is visible in the history
  dict, but it does not affect learning.

### Verification impact

A model trained with `alpha = 0.0` against a correct constraint loss *should*
be more likely to satisfy the property post-training. However, see §3—the
constraint loss is not being called correctly, so in practice no useful gradient
is flowing from either source.

---

## 3. Constraint Function: Broken Call Signature

**File:** `training.py` — line 231–232

### What changed

```python
# vcl-scalar
constraint_loss = constraint_fn(network_fn, parameters["C_safe"], parameters["eps"])

# new-data
print(type(constraint_fn))                    # debug artifact
constraint_loss = constraint_fn()             # no arguments
```

The Vehicle loss function returned by `load_drug_verification_constraints`
requires arguments (at minimum a callable network and parameters). Calling it
with no arguments will raise a `TypeError` at runtime, crashing training.

The commented-out call hints at a new intended signature:
```python
# constraint_fn(parameters["mean"], parameters["std_dev"], network_fn,
#               parameters["C_safe"], parameters["eps"])
```
This is not yet implemented anywhere.

### Training impact

Training via `train_model_with_constraint` **will crash** on the first batch
of the first epoch. No constrained training is currently possible in this branch.

### Verification impact

Since no constraint gradient is flowing, any model saved from this branch has
had **zero constraint-guided training**. Verification is attempted against a
model that was trained purely on simulation MSE (from a prior `train_model`
call, if that path is used instead). Whether it passes verification is
therefore entirely determined by whether the simulation data happened to produce
a model that satisfies `safeFar`—not by any deliberate constraint optimisation.

---

## 4. Vehicle Property: `safeNear` → `safeFar`

**File:** `cli.py` — line 184

### What changed

```python
# vcl-scalar
p.add_argument("--property", default="safeNear", ...)

# new-data
p.add_argument("--property", default="safeFar", ...)
```

These two properties have different semantics in `pk.vcl`:

| Property | Input region | Output condition |
|----------|-------------|-----------------|
| `safeNear` | `conc` near `C_safe` (99–100 % of limit) | Dose output < `eps` (model must withhold drug near the ceiling) |
| `safeFar` | `conc` below `C_safe * 0.99` | Peak concentration after dose < `C_safe` (model must not cause an unsafe spike) |

### Training impact

`safeNear` is a simpler, more conservative property (just force a near-zero
dose). `safeFar` is more directly tied to the oral absorption dynamics and
requires the model to learn how much drug is safe to give given the current
plasma level—a harder constraint to satisfy and a more useful one to train
against.

### Verification impact

`safeFar` is the property that is now also matched by the simulation model (see
§1). Switching to this property is necessary for end-to-end coherence: the
training data is generated with oral absorption dynamics, the constraint encodes
oral absorption dynamics, and the verifier checks the same thing.

The implication is that formal verification now proves something *stronger*:
that for all inputs in the safe region, the model's recommended dose will not
push peak concentration past `C_safe`. This is more meaningful than `safeNear`
alone.

---

## 5. Vehicle Property Loading: `declarations` Hardcoded to `()`

**File:** `vehicle_loss.py` — line 37

### What changed

```python
# vcl-scalar
declarations = loss_tf.load_specification(spec_path, logic=logic,
                                          declarations=properties or ())
# ...
if properties:
    return {name: declarations[name] for name in properties if name in declarations}

# new-data
declarations = loss_tf.load_specification(spec_path, logic=logic,
                                          declarations=())   # always ()
# filtering logic commented out — always returns dict(declarations)
```

Passing `declarations=()` to `load_specification` tells Vehicle to compile
*all* properties rather than only the named ones. The property-name filter is
also commented out, so the returned dict always contains every property in the
spec.

### Training impact

- The `--property` CLI flag is ignored at the loss-loading stage. All properties
  are compiled regardless.
- The dict is passed into the constraint training code. In `cli.py` a single
  property is then selected from this dict (or the whole dict is passed—needs
  checking). If a single function is expected and a dict is received, this
  contributes to the broken call in §3.
- Compiling all properties is slower and uses more memory during training setup.

### Verification impact

Verification itself uses a separate script (`verify.sh`) that calls the Vehicle
CLI directly; this Python loading path does not affect what the verifier proves.
The verification result is therefore not directly degraded by this change.
However, it means the training code cannot selectively load and train against
one property cleanly, which makes it harder to confirm that gradient-based
loss is targeting the intended specification clause.

---

## 6. Scaler Values Passed to Parameters Dict

**File:** `cli.py` — lines 65–66

### What changed

```python
# new-data only
parameters["mean"] = scaler.mean_
parameters["std_dev"] = scaler.scale_
```

These are added to the `parameters` dict immediately after `prepare_data`.
They correspond to the new intended constraint signature seen in the commented-
out call (§3).

### Training impact

No current impact — the constraint call is broken (§3) so these values are
never consumed. When the call signature is fixed, these will allow the
constraint function to re-normalise inputs internally rather than expecting
pre-normalised tensors, which would be the correct approach.

### Verification impact

`update_vcl_scaler` already writes `pk_mean.idx` and `pk_std.idx` so the
Vehicle spec reads the correct normalisation at verify time. This change is
about making the *training-time* constraint aware of the same normalisation.
Once §3 is fixed this will be necessary for training and verification to use
the same numerical normalisation.

---

## 7. Scaler Export: `.vcl` Rewriting Replaced by `.idx` Files

**File:** `training.py` — `update_vcl_scaler`

*(Present in both branches but the VCL inline-rewriting is commented out in
`new-data`.)*

The direct regex rewrite of `pk.vcl` is replaced by writing binary `.idx`
files (`pk_mean.idx`, `pk_std.idx`). The `@dataset` annotation in `pk.vcl`
means Vehicle reads these files at verify time.

### Verification impact

This is a correct approach: the `.idx` files are the authoritative source of
normalisation constants, and the inline comment values in `pk.vcl` are now
documentation only. As long as `pk_mean.idx` / `pk_std.idx` are regenerated
on every training run *before* verification, normalisation is consistent.
If these files are stale (e.g. from a different training run), verification
silently applies the wrong normalisation, invalidating the proof—the same risk
as before, just with a different file.

---

## 8. Dependency and Runtime Changes

**File:** `pyproject.toml`

| Change | Reason / Impact |
|--------|----------------|
| `requires-python >= 3.11` (was 3.12) | Widens compatibility; no functional effect. |
| `tf2onnx` added | Required for `export_onnx` in `training.py`. This was already present in the vcl-scalar code but missing from the declared dependencies. The ONNX export path (including the positive-clamp epsilon node) is unchanged. |

---

## Summary: Current State vs. Verification Readiness

| Area | vcl-scalar | new-data | Net effect |
|------|-----------|----------|-----------|
| PK model | Euler (IV bolus) | Oral absorption (superposition) | Better realism; new `conc` inconsistency |
| Spec alignment | `safeNear` + Euler | `safeFar` + oral absorption | **Improved** — model and spec now agree on dynamics |
| Constraint training | Working (alpha=0.5) | Broken (`constraint_fn()` crashes) | **Regression** — no constraint gradient |
| Property filter | Correct | Ignored (all props loaded) | Loss loading unreliable |
| Scaler sync | `.vcl` rewrite | `.idx` files | Equivalent if files are fresh |

### Critical blockers before verification is meaningful

1. **Fix `constraint_fn()` call signature** in `training.py:232`. The new
   signature must match whatever `load_drug_verification_constraints` actually
   returns, and the `mean`/`std_dev` parameters need to be threaded through
   correctly.

2. **Resolve `conc` semantics**: decide whether the feature and the PD
   dynamics should use peak, trough, or average concentration within each
   12-hour interval, and apply that consistently so that the trained model's
   input distribution matches the verified input domain.

3. **Restore property filtering** in `vehicle_loss.py` so that
   `load_drug_verification_constraints` returns only the intended property and
   the constraint training targets precisely `safeFar`.

4. **Set `alpha > 0`** (or justify `alpha = 0.0`) to ensure the model retains
   clinical dose fidelity alongside constraint satisfaction. A model that
   satisfies `safeFar` by always outputting a near-zero dose passes
   verification but is therapeutically useless.
