# NeSy Paper Proposal

## Subject Area

**Primary: Specification and verification of machine/deep learning systems**

The central contribution is a complete neurosymbolic pipeline in which clinical
safety properties are written as formal symbolic specifications in Vehicle's `.vcl`
language, compiled by Vehicle into differentiable TensorFlow loss functions that
constrain training, and then verified post-training against the exported ONNX model
using Marabou. The symbolic and neural components are not loosely coupled — the same
formal specification that drives training is the one that is proven to hold.

**Secondary: Informed (physics-aware) Machine Learning**

The safety specifications are derived from the one-compartment pharmacokinetic (PK)
equations. The `safeFar` property is not a heuristic bound — it encodes the actual
closed-form expression for peak post-dose concentration under first-order absorption,
meaning the symbolic constraint is grounded in the physical dynamics of drug
distribution. The network is constrained by biochemical law, not just labelled data.

---

## Proposed Title

**Adaptive Neurosymbolic Constraint Balancing for Formally Verified Clinical Dosing:
GradNorm-Weighted Property-Driven Training with Vehicle, Marabou, and Rocq**

---

## Abstract

We present a neurosymbolic training and verification pipeline for a neural dosing
recommender in a safety-critical pharmacokinetic (PK) setting. Clinical safety
requirements are formalised as symbolic properties in Vehicle's specification
language and compiled into differentiable constraint losses. Training proceeds in two
phases: a task-only phase in which the network learns clinically reasonable dose
predictions, followed by a constrained phase in which GradNorm adaptively rebalances
the task loss against two symbolic constraint losses in real time, avoiding the
manual alpha-tuning of prior fixed-weight approaches. After training, the network is
exported to ONNX and all nine properties — including the two non-trivial safety
properties `safeFar` and `safeNear` — are formally verified by Marabou, which proves
no counterexample exists in the specified input domain. Crucially, Marabou's
single-step guarantee is then lifted to infinite-horizon safety by an inductive
invariant proof in Rocq: the theorem `doses_safe` proves by induction on the number
of doses that total plasma concentration remains within `[0, C_safe]` for all n and
all times t, with the Marabou result supplying the single-step invariant hypothesis.
The verified network achieves a mean absolute dosing error of 4.8 mg (35% lower than
a fixed-weight baseline) with r = 0.996 correlation to the target controller. We
report the engineering challenges that arise when integrating differentiable symbolic
constraints into adaptive loss balancing — including gradient path breakage, loss
scale collapse, and optimiser state corruption at phase transition — and the
solutions developed.

---

## 1. Introduction and Motivation

Underdosing and overdosing in intravenous drug therapy are both consequential: the
former prolongs illness, the latter can cause organ toxicity. Clinical dosing
controllers derived from pharmacokinetic models can be formally analysed, but neural
dosing recommenders — which can adapt to individual patient covariates — typically
offer no safety guarantees. This creates a tension: the flexibility of learned models
versus the certifiability of symbolic rules.

Neurosymbolic AI offers a path through this tension. If safety properties can be
expressed symbolically, compiled into training signals, and then verified formally
against the trained network, the resulting model is both adaptive and certifiable.
This paper describes such a pipeline applied to a one-compartment PK dosing task,
and characterises the practical difficulties that arise when the symbolic constraint
losses interact with adaptive gradient-based optimisation.

The specific safety requirements are:

- **safeFar**: when current plasma concentration is well below the safe ceiling
  (C ≤ 0.99 · C_safe), the recommended dose must not push peak concentration above
  C_safe. This bound is derived from the closed-form PK peak concentration equation.
- **safeNear**: when current concentration is already near the ceiling
  (0.99 · C_safe ≤ C ≤ C_safe), the recommended dose must be near-zero (< 0.001 mg).
- **nonNeg**: the recommended dose must be non-negative everywhere.

These are specified in Vehicle's `.vcl` language as universally quantified properties
over the input domain:

```
safeFar = forall x . safeFarInput x => safeFarOutput x
safeNear = forall x . safeNearInput x => safeNearOutput x
```

where `safeFarOutput` encodes the pharmacokinetic peak concentration formula
directly. Vehicle compiles these into TensorFlow constraint losses; Marabou proves
them against the ONNX export.

---

## 2. Related Work

**Property-driven training / constraint learning.** Several works have incorporated
symbolic constraints into neural training via differentiable penalties (e.g.,
Xu et al. 2018, semantic loss; Fischer et al. 2019, DL2). This work uses Vehicle
as the constraint compiler, which targets formal verification as well as training —
the same specification is used for both.

**Neural network verification.** Marabou (Katz et al. 2019) and related tools
(α,β-CROWN; VNN-LIB benchmarks) verify properties of fixed, trained networks.
Verification-aware training (e.g., IBP, CROWN-IBP) trains networks to be easier
to verify. This work takes a softer approach: constraint losses push the network
toward a safe region, with no interval-bound propagation during training, and
post-hoc verification confirms the result.

**Vehicle.** Daggitt et al. (2022, 2024) introduced Vehicle as a specification
language and toolchain for neural network properties. Prior Vehicle applications
have focused on post-hoc verification; this work uses Vehicle's loss compiler to
integrate specifications into training, combining both uses in one pipeline.

**GradNorm.** Chen et al. (ICML 2018) proposed GradNorm for multi-task learning,
adapting per-task loss weights based on gradient norms and relative training rates.
This paper applies GradNorm to the constraint-vs-task trade-off in
property-driven training, where the "tasks" are the symbolic safety constraints and
the supervised dosing objective.

**Proof assistants for neural system safety.** Proof assistants (Coq/Rocq, Isabelle,
Lean) have been used to formalise properties of neural network verifiers themselves
(e.g., Lammich et al. on Marabou soundness), but their use to prove infinite-horizon
properties of a specific trained network — with the neural network verification
result as an axiom — is less explored. This work uses Rocq to prove an inductive
invariant over sequences of network evaluations, a step that is beyond what neural
network verifiers such as Marabou can express natively.

**Pharmacokinetic modelling.** One-compartment PK models with first-order absorption
and elimination are standard in clinical pharmacology. Neural surrogates for PK
systems have been studied, but formal verification of their safety properties in a
training pipeline has not, to our knowledge.

---

## 3. Method

### 3.1 Problem setup

A feedforward network `pk : R^5 → R^+` maps patient state
(plasma concentration C, temperature T, WBC count, age, weight) to a recommended
dose in mg. It is trained against a simulated cohort of 50 patients × 47 timesteps
generated from the one-compartment PK model with patient-specific Ka, Ke, Vd.

### 3.2 Symbolic specification (Vehicle)

Safety properties are written in `pk.vcl`. `safeFar` encodes:

```
safeFarOutput x = let y = (normpk(x)[0] * Ka) / (Vd * (Ka - Ke)) in
    x[conc] + y * (Ke_over - Ka_under) < C_safe
```

where the right-hand side is the PK closed-form for peak post-dose concentration.
`safeNear` requires the output to be less than ε = 0.001 mg when the patient is
already near C_safe. Normalisation parameters (mean, std) from the input scaler are
inlined as literals so that Vehicle's compiled loss and the inference-time
normalisation are provably consistent.

Vehicle compiles each property to a TensorFlow loss function via its vehicle-loss
backend. The `safeFar` spec requires parameter inlining (Ka, Ke, Vd as literals)
because Vehicle's symbolic evaluator collapses `@parameter` branches to constants,
eliminating the gradient signal; this is resolved by generating a temporary `.vcl`
with all PK parameters as literals at training time.

### 3.3 Two-phase GradNorm training

**Phase 1 (epochs 1–N):** task loss only. The network learns a clinically reasonable
dose prediction before constraints are introduced. Without this phase, constraint
gradients (magnitude ~14,000 at epoch 1) overwhelm the task signal and drive
predictions toward zero — formally safe but clinically useless.

**Phase 2 (epochs N+1–end):** GradNorm balances three losses:
- `L_task`: MSE between predicted and target dose (in normalised dose space)
- `L_safeFar`: Vehicle-compiled constraint loss for `safeFar`
- `L_safeNear`: Vehicle-compiled constraint loss for `safeNear`

GradNorm maintains a weight vector `w ∈ R^3` updated each batch:

```
target_norm_i = mean_grad_norm * (L_i / L_i^0 / mean(L_j / L_j^0))^alpha
grad_norm_loss = sum_i |w_i * ||∇_W L_i|| - target_norm_i|
```

Weights sum to n_tasks = 3 and are floored at min_weight = 0.05 to prevent any
loss from being zeroed out.

**Engineering challenges and fixes:**

1. *Loss scale collapse.* Raw dose MSE (~25,000 mg²) was four orders of magnitude
   larger than constraint losses (~1.0), causing GradNorm to collapse the task
   weight immediately. Fix: y-normalisation (StandardScaler on y_train); all losses
   are additionally divided by their initial values so all three start at ~1.0.

2. *Gradient path breakage.* `tape.gradient(total_loss, model_variables)` returned
   zeros because the weighted sum was assembled outside the GradientTape context.
   Fix: per-loss gradients computed individually inside the tape, then combined
   manually: `g = w_0 * g_task/L_0^0 + w_1 * g_con1/L_1^0 + w_2 * g_con2/L_2^0`.
   This is mathematically equivalent to differentiating the normalised weighted sum.

3. *Optimiser state corruption at phase transition.* Adam accumulated second-moment
   estimates calibrated to task-only gradients during phase 1. When constraint
   gradients (up to ~1000× larger) arrived at epoch N+1, the effective Adam step
   size was enormous. Fix: reset Adam at phase_switch with `clipnorm=1.0`.

### 3.4 Marabou verification (single-step)

The trained Keras model is exported to ONNX with a ReLU + Add(0.0001) appended
post-hoc to enforce non-negativity by construction. Vehicle runs Marabou as a
back-end to check all nine properties against the ONNX model.

Marabou's verification is bounded: it proves that for any single input in the
specified domain, the network's output satisfies the property. It cannot natively
reason about infinite sequences of inputs or about how the system evolves when the
network's output becomes the next timestep's input. The Rocq proof addresses this.

### 3.5 Rocq inductive invariant (infinite-horizon)

The Rocq files (`Rocq/Spec.v`, `Rocq/proof.v`) formalise the multi-dose PK dynamics
and prove infinite-horizon safety by mathematical induction.

**Concentration model.** The total plasma concentration after n doses is the
superposition of individual PK curves, each shifted to its administration time:

```
total_conc Ds t = Σ_i max(0, Concentration(D_i, t − ttd · i))
```

where `Concentration D t = (D·Ka / (Vd·(Ka−Ke))) · (e^{−Ke·t} − e^{−Ka·t})` is the
one-compartment absorption/elimination profile and `ttd` is the inter-dose interval.

**Dose sequence.** `n_doses initial n` is defined recursively: each dose is the
network's output given the total concentration at the corresponding dosing time,
capturing the closed-loop feedback between doses.

**Single-step invariant.** The bridge between Marabou and Rocq is the lemma `safe`:

```
safe : ∀ C, 0 ≤ C ≤ C_safe →
    C + Concentration(network(C), dCdt_root) ≤ C_safe
```

This is derived from `safeFar` and `safeNear` (proven by Marabou) by case split on
whether C ≤ 0.99·C_safe or C ≥ 0.99·C_safe:
- If C ≤ 0.99·C_safe, `safeFar` directly gives the peak bound.
- If C ≥ 0.99·C_safe, `safeNear` gives dose ≈ 0, so peak ≈ 0 and C + 0 ≤ C_safe.

The Rocq proof also requires auxiliary lemmas about the PK ODE: that
`Concentration D` is differentiable, that its derivative is zero exactly at
`dCdt_root = ln(Ka/Ke)/(Ka−Ke)`, and that `dCdt_root` is the global maximum of
the concentration curve — so evaluating at `dCdt_root` gives the peak.

**Inductive theorem.**

```
doses_safe : ∀ (n : nat) (initial t : R),
    0 ≤ initial ≤ C_safe →
    0 ≤ total_conc (n_doses initial n) t ≤ C_safe
```

The proof is by strong induction on n. The base case (n = 0) follows from `safe`
and `non_neg`. The inductive step uses `safe` applied to the concentration at the
next dosing time (supplied by the inductive hypothesis) plus the `unfold_n_dose_once`
lemma which expresses `total_conc` at step n+1 in terms of step n.

**Top-level theorem.**

```
pk_safe : ∀ (n : nat) (t : R) (s : state),
    safeInput s →
    0 ≤ total_conc (n_doses (C s) n) t ≤ C_safe
```

`pk_safe` instantiates `doses_safe` with the actual network (expressed as a Rocq
function wrapping `normpk`), using `safeInput` as the precondition. Together with
the Marabou proof, this closes the chain: the trained network is safe not just for
one evaluation but for any number of doses applied over time to any patient whose
initial state is within the verified domain.

**Formal chain summary:**

```
Vehicle .vcl spec
    ↓  compile (Vehicle loss backend)
Differentiable constraint losses → GradNorm training
    ↓  export ONNX
Marabou: proves safeFar ∧ safeNear ∧ nonNeg  (single step)
    ↓  safe lemma (case split)
Rocq: doses_safe by induction on n           (all n steps, all t)
    ↓  pk_safe instantiation
Infinite-horizon safety guarantee
```

---

## 4. Results

### Formal verification

All 9 properties were verified by Marabou. 6 were trivially discharged (structural
PK parameter bounds). 3 required Marabou to search for counterexamples:

| Property | Queries | Result |
|----------|---------|--------|
| safeFar  | 1/1     | Marabou proved no counterexample exists |
| safeNear | 1/1     | Marabou proved no counterexample exists |
| nonNeg   | 1/1     | Marabou proved no counterexample exists |

The Rocq theorem `doses_safe` then uses `safeFar` and `safeNear` as axioms
(hypotheses `safe` and `non_neg`) to prove that total plasma concentration remains
in `[0, C_safe]` for all `n ∈ ℕ` and all `t ∈ ℝ≥0`. The top-level theorem
`pk_safe` connects this to the actual network, completing the infinite-horizon
safety proof.

### Accuracy and clinical relevance

| Metric                  | Fixed-weight baseline | GradNorm (this work) |
|-------------------------|-----------------------|----------------------|
| Test MAE                | 7.4 mg                | **4.8 mg**           |
| Max absolute error      | 260 mg                | **146 mg**           |
| Corr(true, pred)        | 0.989                 | **0.996**            |
| Pred std / True std     | ~1.00                 | 1.030                |
| High-severity dose ratio| ~3.5×                 | **4.45×**            |

GradNorm achieves 35% lower MAE and 44% lower maximum error than the fixed-weight
baseline, while both achieve full formal verification. The network is not a flat
conservative predictor: predictions for high-fever, high-WBC patients are 4.45×
higher than for near-normal patients, and correlation with the target controller
is r = 0.996.

Worst-case errors (max 146 mg) occur at timestep 0–1 for high-severity patients
with zero initial concentration — first-dose underdosing, not overdosing. This is
a suboptimal but not safety-violating failure mode; all formal properties hold.

---

## 5. Key Contributions

1. **End-to-end neurosymbolic pipeline**: Vehicle specification → differentiable
   constraint loss → GradNorm-balanced training → Marabou formal verification,
   applied to a safety-critical clinical dosing task.

2. **GradNorm for symbolic constraint balancing**: first application of GradNorm
   to the trade-off between a supervised task loss and Vehicle-compiled symbolic
   constraint losses, with characterisation of the loss scale, gradient path, and
   optimiser state problems this introduces.

3. **Physics-grounded symbolic constraints**: the `safeFar` specification encodes
   the closed-form PK peak concentration equation as a formal property, making the
   safety guarantee physically meaningful — not a proxy bound.

4. **Empirical comparison with fixed-weight PDT**: ablation showing that adaptive
   balancing reduces MAE by 35% and max error by 44% over a fixed-alpha baseline,
   with both achieving full formal verification.

5. **Two-tier verification: Marabou + Rocq.** Marabou proves the single-step
   invariant for the fixed network; Rocq proves by induction that this single-step
   bound is preserved across all n doses. This separation of concerns — bounded
   neural verification for the per-step property, proof assistant for the
   infinite-horizon consequence — is a reusable architectural pattern for
   safety-critical closed-loop neural systems.

6. **Documented engineering failures**: explicit account of three non-obvious
   failure modes (loss scale collapse, tape gradient breakage, optimiser state
   corruption) encountered when integrating GradNorm with a symbolic constraint
   compiler, with minimal reproducible fixes.

---

## 6. Future Work

- **First-dose error.** The systematic underdose at timestep 0 (no drug on board,
  high severity) suggests a loading-dose rule could be incorporated as an
  additional symbolic constraint or an explicit network input.
