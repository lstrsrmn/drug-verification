CHANGE: Property-driven training (PDT) with GradNorm constraint balancing
Branch: trial/pdt-training
Files changed: src/drug_verification/grad_norm.py (new),
               src/drug_verification/vehicle_loss.py,
               src/drug_verification/training.py,
               src/drug_verification/cli.py,
               src/drug_verification/tuning.py

Goal

The goal of this branch is to teach
the network to satisfy those property safeNear and safeFar during training by using the
Vehicle-compiled constraint losses as soft penalties, balanced against the
task loss (MSE on dose prediction) using GradNorm adaptive loss weighting.

Approach

GradNorm (Chen et al., ICML 2018) adapts per-task loss weights online so
that each loss trains at a similar rate. The three losses are:

    task            MSE between predicted and target dose
    safeFar         Vehicle-compiled loss for the safeFar property
    safeNear        Vehicle-compiled loss for the safeNear property

A new module grad_norm.py implements GradNorm for three tasks. It maintains
a tf.Variable weight vector that is updated each batch using a separate Adam
optimiser, with weights projected to sum to n_tasks=3 and floored at
min_weight to prevent any single loss from being zeroed out.

The training loop in train_model_with_constraint uses a persistent
GradientTape to compute all three losses in a single forward pass and applies
the combined weighted gradient to the model with a single Adam step.

Two loading strategies are used for the Vehicle properties (documented fully
in vehicle_loss.py):

    safeFar     Compiled from a generated temporary spec with PK parameters
                and scaler values inlined as literals. This resolves an
                if/else branch on Ka/Ke that causes the loss compiler to
                collapse to a constant when loaded from pk.vcl directly.

    safeNear    Loaded directly from pk.vcl. Vehicle 0.24.1 resolves
                @parameter declarations correctly and handles negation
                through forall. Extra arguments (scaler arrays, C_safe, eps)
                are bound via closure so the returned callable only requires
                the network.

A PTY workaround is also applied at import time: vehicle_lang.session uses
PTY-based stdout capture which returns an empty string when TensorFlow has
already initialised (TF initialises at import time and interferes with PTY
capture). The module-level check_output function is patched to use
Session.check_output (which uses redirect_stdout instead) to avoid this.

y-target normalisation

The task loss MSE was initially ~25,000 (doses in raw mg) while Vehicle
constraint losses are ~1.0. This four-order-of-magnitude scale difference
caused GradNorm to immediately collapse the task weight toward zero, leaving
the model unable to learn predictions at all.

Fix: y_train and y_test are now scaled with a StandardScaler fitted on
y_train only (matching the existing X scaler pattern). The model is trained
in normalised dose space. train_model_with_constraint receives y_mean and
y_std and wraps the model's network_fn to de-normalise output before passing
to the Vehicle constraint functions, which still expect doses in physical
units (mg). evaluate_model accepts an optional y_scaler and inverse-transforms
predictions before computing metrics so reported errors are in mg.

The y scaler mean and std are saved to pk_y_mean.idx and pk_y_std.idx
alongside the existing pk_mean.idx / pk_std.idx X scaler files.

GradNorm min_weight raised from 1e-3 to 0.2

The original default of 1e-3 allowed any task weight to effectively reach
zero. With the y-normalisation fix bringing all three losses to ~1.0 scale,
a floor of 0.2 (6.7% of gradient signal per task minimum) is sufficient to
prevent collapse while still allowing GradNorm to rebalance meaningfully.

Gradient connectivity check

A pre-training check was added to train_model_with_constraint that verifies
both constraint functions produce non-None gradients w.r.t. model variables
before the epoch loop starts. If all gradients are None, a warning is emitted
immediately rather than allowing 100 epochs of silent no-op constraint
training.

Current status and known issues
--------------------------------

The branch is not yet complete. Two persistent problems remain unresolved
after the y-normalisation and GradNorm fixes.

Problem 1: All three losses are frozen across all training epochs

Across every training run attempted, task loss, val loss, and both constraint
losses are completely static from epoch 1 through epoch 100. The model makes
identical predictions throughout training; no weights move meaningfully.

Observed behaviour (representative run after all fixes):

    Epoch  1/100 — task: 1.1120, safeFar: 4.7975, safeNear: 86.6127, val: 1.1524
    Epoch  5/100 — task: 1.1126, safeFar: 4.7975, safeNear: 86.6127, val: 1.1524
    Epoch 10/100 — task: 1.1119, safeFar: 4.7975, safeNear: 86.6127, val: 1.1524

The constraint losses change correctly between runs when network_fn changes
(e.g. after y-normalisation the values shifted from 1.22/0.59 to 4.79/86.6),
confirming Vehicle does pick up the network at initialisation. But within a
run the values never change regardless of model weight updates.

Problem 2: GradNorm feedback loop from constraint scale mismatch

Even when constraint losses are not frozen, the scale difference between the
task loss (~1.0 after y-normalisation) and safeNear (~86.6) triggers a
GradNorm pathology: GradNorm interprets safeNear's large gradient norms as
meaning safeNear is training too slowly, and down-weights it toward the
min_weight floor. The task weight is simultaneously up-weighted but the
safeNear gradient (86x larger than task) still dominates the model update,
pushing model weights in directions that do not reduce any of the three losses.

Suspected root cause (?)
--------------------------------------------------

The frozen constraint losses strongly suggest a TensorFlow function tracing
and caching issue in the Vehicle TF loss backend.

When constraint_fn(pk=network_fn) is called the first time inside the
training loop's GradientTape, TF traces the Vehicle compiled function and
embeds a static computation graph. We believe the trace captures the output
values of network_fn at specific spec-defined input points as constants,
rather than embedding them as live variable-read ops. On all subsequent calls
the cached trace is reused, returning the same values regardless of model
weight changes.

Evidence:

1.  The gradient connectivity check (run once before training, inside a fresh
    GradientTape) passes: 6/6 model variables have non-None gradients for
    both constraint functions. This confirms the Vehicle function does compute
    through the model on its first call.

2.  Constraint losses are identical to 4 decimal places across all 100 epochs,
    regardless of which GradNorm configuration, learning rate, or loss scaling
    is used.

3.  The values differ correctly between runs when the network changes (the
    fresh call at the gradient check picks up the new network), but never
    within a run (all subsequent training-loop calls return cached values).

4.  The same frozen-loss behaviour was observed with raw (un-normalised) y
    targets and with normalised y targets, ruling out loss scaling as the cause.

The pre-training gradient check passing while the training loop is frozen is
consistent with TF retracing on the first call (inside the check's tape) but
reusing a cached trace for all training-loop calls.

Next steps 

1.  If Vehicle confirms a fix or correct calling pattern, apply it and retest
    the full constrained training loop.