"""Neural network training, evaluation, and export."""

import tensorflow as tf
from tensorflow.keras import models, layers
from sklearn.model_selection import train_test_split
from sklearn.preprocessing import StandardScaler
import idx2numpy

from . import constants as C
from .grad_norm import GradNorm


def build_model(input_size, hidden_sizes=C.DEFAULT_HIDDEN_SIZES):
    """Build a feedforward Keras model for dose prediction."""
    layer_list = [layers.Input(shape=(input_size,))]
    for size in hidden_sizes:
        layer_list.append(layers.Dense(size, activation="relu"))
    layer_list.append(layers.Dense(1, activation="linear"))

    model = models.Sequential(layer_list)
    model.compile(optimizer="adam", loss="mse", metrics=["mae"])
    return model


def prepare_data(X, y, test_size=C.DEFAULT_TEST_SIZE, seed=C.DEFAULT_SEED):
    """Scale features and split into train/test sets.

    Both X and y are scaled using StandardScaler fit on the training split
    only to avoid data leakage. Scaling y brings the task loss to ~1.0,
    matching the scale of Vehicle constraint losses for stable GradNorm training.

    Returns (X_train, X_test, y_train, y_test, scaler, y_scaler).
    """
    y = y.reshape(-1, 1) if y.ndim == 1 else y

    X_train_raw, X_test_raw, y_train_raw, y_test_raw = train_test_split(
        X, y, test_size=test_size, random_state=seed
    )

    import numpy as np
    scaler = StandardScaler()
    scaler.fit(X_train_raw)
    # Floor std to avoid near-zero division when features have very low variance
    # (e.g. trough concentrations ~0 with fast elimination). Without this the
    # Vehicle spec normalisation overflows to NaN for inputs outside training range.
    scaler.scale_ = np.maximum(scaler.scale_, 1e-2)
    X_train = scaler.transform(X_train_raw)
    X_test = scaler.transform(X_test_raw)

    y_scaler = StandardScaler()
    y_train = y_scaler.fit_transform(y_train_raw)
    y_test = y_scaler.transform(y_test_raw)

    return X_train, X_test, y_train, y_test, scaler, y_scaler


def train_model(
    model,
    X_train,
    y_train,
    X_val,
    y_val,
    epochs=C.DEFAULT_EPOCHS,
    batch_size=C.DEFAULT_BATCH_SIZE,
):
    """Train the model and return the history object."""
    history = model.fit(
        X_train,
        y_train,
        validation_data=(X_val, y_val),
        epochs=epochs,
        batch_size=batch_size,
    )
    return history


def evaluate_model(model, X_test, y_test, y_scaler=None):
    """Evaluate model on the test set.

    If y_scaler is provided, predictions and targets are inverse-transformed
    before computing metrics so errors are reported in physical units (mg).

    Returns a dict with mse, mae, and max_absolute_error.
    """
    import numpy as np
    preds = model.predict(X_test, verbose=0)
    if y_scaler is not None:
        preds = y_scaler.inverse_transform(preds.reshape(-1, 1))
        y_test = y_scaler.inverse_transform(np.array(y_test).reshape(-1, 1))
    errors = preds - y_test
    mse = float(tf.reduce_mean(tf.square(errors)).numpy())
    mae = float(tf.reduce_mean(tf.abs(errors)).numpy())
    max_ae = float(tf.reduce_max(tf.abs(errors)).numpy())
    return {"mse": mse, "mae": mae, "max_absolute_error": max_ae}


def update_vcl_scaler(scaler, y_scaler=None, spec_path="pk.vcl"):
    """Rewrite the normalisation constants in a Vehicle spec file to match a fitted scaler.

    The Vehicle spec embeds mean and std values used to normalise inputs before
    passing them to the network (see `normalise` in pk.vcl). These must exactly
    match the StandardScaler fitted during training — if they diverge, the
    verified property applies to a *different* normalisation than the exported
    ONNX model uses, silently invalidating the formal proof.

    This function rewrites only the two value lines in-place, leaving all other
    spec content unchanged. It should be called immediately after prepare_data()
    and before any export or verification step.

    Args:
        scaler: A fitted sklearn StandardScaler.
        spec_path: Path to the .vcl file to update.
    """
    import re

    mean_str = ", ".join(f"{v:.8g}" for v in scaler.mean_)
    std_str = ", ".join(f"{v:.8g}" for v in scaler.scale_)

    with open(spec_path, "r") as f:
        content = f.read()

    # Replace the value lines; patterns are anchored to the assignment so that
    # the type declaration lines above them are left untouched.
    content = re.sub(
        r"(meanScalingValues\s*=\s*)\[.*?\]",
        rf"\g<1>[{mean_str}]",
        content,
    )
    content = re.sub(
        r"(standardDeviationValues\s*=\s*)\[.*?\]",
        rf"\g<1>[{std_str}]",
        content,
    )

    with open(spec_path, "w") as f:
        f.write(content)

    print(f"Updated {spec_path} with scaler values from this training run.")
    print(f"  meanScalingValues        = [{mean_str}]")
    print(f"  standardDeviationValues  = [{std_str}]")

    if y_scaler is not None:
        print(f"  y_mean (dose scaler)     = {y_scaler.mean_[0]:.8g}")
        print(f"  y_std  (dose scaler)     = {y_scaler.scale_[0]:.8g}")


def export_onnx(model, out_path="models/pk.onnx", positive_clamp=True):
    """Export a Keras model to ONNX format.

    If positive_clamp is True (default), appends a constant Add node to the
    ONNX graph that shifts the output by +0.0001, guaranteeing output > 0
    for the nonNeg verification property.
    """
    import tf2onnx
    import onnx
    from onnx import numpy_helper, TensorProto
    import numpy as np

    input_sig = [tf.TensorSpec(model.input_shape, tf.float32, name="input")]
    onnx_model, _ = tf2onnx.convert.from_function(
        tf.function(model, input_signature=input_sig),
        input_signature=input_sig,
    )

    if positive_clamp:
        graph = onnx_model.graph

        # The current graph output tensor name
        original_output = graph.output[0].name

        # Add Relu to clamp negatives to zero (training uses linear output,
        # so the exported model must enforce non-negativity explicitly)
        rectified_output = original_output + "_rectified"
        relu_node = onnx.helper.make_node(
            "Relu",
            inputs=[original_output],
            outputs=[rectified_output],
        )
        graph.node.append(relu_node)

        # Add a scalar constant initializer for the epsilon value
        epsilon_name = "positive_clamp_epsilon"
        epsilon_tensor = numpy_helper.from_array(
            np.array([0.0001], dtype=np.float32), name=epsilon_name
        )
        graph.initializer.append(epsilon_tensor)

        # Add an Add node: shifted = relu(original) + 0.0001
        shifted_output = original_output + "_shifted"
        add_node = onnx.helper.make_node(
            "Add",
            inputs=[rectified_output, epsilon_name],
            outputs=[shifted_output],
        )
        graph.node.append(add_node)

        # Update the graph output to point to the shifted tensor
        graph.output[0].name = shifted_output
        # Update the type/shape info to match
        shifted_type = onnx.helper.make_tensor_value_info(
            shifted_output,
            TensorProto.FLOAT,
            [None, 1],
        )
        graph.output.pop()
        graph.output.append(shifted_type)

    onnx.save(onnx_model, out_path)
    print(f"Saved ONNX model to: {out_path}" + (" (with positive clamp)" if positive_clamp else ""))
    return onnx_model


def train_model_with_constraint(
    model,
    X_train,
    y_train,
    X_val,
    y_val,
    constraint_fn,
    y_mean,
    y_std,
    alpha=C.DEFAULT_GRADNORM_ALPHA,
    gradnorm_lr=C.DEFAULT_GRADNORM_WEIGHT_LR,
    initial_constraint_weight=C.DEFAULT_INITIAL_CONSTRAINT_WEIGHT,
    optimizer_lr=C.DEFAULT_OPTIMIZER_LR,
    objective_constraint_weight=C.DEFAULT_TUNE_CONSTRAINT_OBJECTIVE_WEIGHT,
    trial=None,
    epochs=C.DEFAULT_EPOCHS,
    batch_size=C.DEFAULT_BATCH_SIZE,
    phase_switch=0,
    verbose=True,
):
    """Train with task loss + safe constraint loss balanced by GradNorm.

    Uses a persistent GradientTape loop so that both losses can be
    backpropagated and their weights adapted online via GradNorm.

    The constraint function takes a single keyword argument: pk=network_fn.
    All spec parameters (Ka, Ke, Vd, scaler values etc.) are inlined in the
    generated training spec and do not need to be passed here.

    Args:
        model: Keras model.
        X_train, y_train: Training data.
        X_val, y_val: Validation data.
        constraint_fn: Compiled safe loss callable.
        y_mean: Mean from the y StandardScaler (scalar). Used to de-normalise
            model output before passing to Vehicle constraint functions, which
            expect doses in physical units (mg).
        y_std: Scale from the y StandardScaler (scalar).
        alpha: GradNorm restoring-force exponent (Chen et al., 2018).
        gradnorm_lr: Learning rate for GradNorm's weight optimizer.
        initial_constraint_weight: Initial relative weight for safe loss.
        optimizer_lr: Learning rate for model parameter optimizer.
        objective_constraint_weight: safe coefficient in Optuna objective metric.
        trial: Optional Optuna trial for pruning support.
        epochs: Number of training epochs.
        batch_size: Batch size.
        phase_switch: If > 0, train on task loss only for this many epochs then
            switch on GradNorm constraint balancing. 0 = constraints active from epoch 1.
        verbose: Whether to print per-epoch logs.

    Returns:
        dict with per-epoch history: task/constraint/total losses,
        val_loss, grad_norm_loss, objective_metric, and adaptive weights.
    """
    optimizer = tf.keras.optimizers.Adam(learning_rate=optimizer_lr)
    dataset = tf.data.Dataset.from_tensor_slices((X_train, y_train))
    dataset = dataset.shuffle(len(X_train)).batch(batch_size)

    grad_norm = GradNorm(
        alpha=alpha,
        weight_lr=gradnorm_lr,
        initial_constraint_weight=initial_constraint_weight,
        min_weight=C.DEFAULT_GRADNORM_MIN_WEIGHT,
    )

    # De-normalise model output before passing to Vehicle constraint functions.
    # The model is trained on normalised doses (mean=0, std=1) but the Vehicle
    # spec formulas expect doses in physical units (mg).
    _y_mean = float(y_mean)
    _y_std = float(y_std)

    def network_fn(x):
        normalised = tf.reshape(model(tf.reshape(x, [1, -1]), training=True), [-1])
        return normalised * _y_std + _y_mean

    # Verify constraint function backpropagates through the model before training.
    with tf.GradientTape() as _tape:
        _loss = constraint_fn(pk=network_fn)
    _grads = _tape.gradient(_loss, model.trainable_variables)
    if all(g is None for g in _grads):
        import warnings
        warnings.warn(
            "constraint_fn produces no gradients w.r.t. model variables. "
            "The Vehicle compiled function may not be connected to the model graph — "
            "constraint losses will not drive training."
        )
    elif verbose:
        n_none = sum(1 for g in _grads if g is None)
        print(f"Gradient check constraint_fn: OK ({len(_grads) - n_none}/{len(_grads)} variables have gradients)")

    history = {
        "task_loss": [], "constraint_loss": [],
        "total_loss": [], "val_loss": [], "grad_norm_loss": [],
        "objective_metric": [], "task_weight": [], "constraint_weight": [],
    }

    for epoch in range(epochs):
        epoch_task = epoch_constraint = 0.0
        epoch_total = epoch_grad_norm = 0.0
        epoch_task_w = epoch_con_w = 0.0
        n_batches = 0
        constraint_active = (phase_switch == 0) or (epoch >= phase_switch)

        # Reset optimizer at the phase boundary so Adam's second moment estimates
        # from task-only training don't inflate effective step sizes when the much
        # larger constraint gradients first appear.
        if phase_switch > 0 and epoch == phase_switch:
            optimizer = tf.keras.optimizers.Adam(
                learning_rate=optimizer_lr, clipnorm=1.0
            )
            if verbose:
                print(f"Epoch {epoch + 1}: resetting optimizer for constraint phase.")

        for x_batch, y_batch in dataset:
            with tf.GradientTape(persistent=True) as tape:
                preds = model(x_batch, training=True)
                task_loss = tf.reduce_mean(tf.square(preds - y_batch))
                if constraint_active:
                    constraint_loss = tf.cast(
                        tf.reduce_mean(constraint_fn(pk=network_fn)), tf.float32
                    )
                else:
                    constraint_loss = tf.constant(0.0)

            if constraint_active:
                batch_info = grad_norm.balance(
                    task_loss=task_loss,
                    constraint_loss=constraint_loss,
                    tape=tape,
                    model_optimizer=optimizer,
                    model_variables=model.trainable_variables,
                )
            else:
                grads = tape.gradient(task_loss, model.trainable_variables)
                optimizer.apply_gradients(zip(grads, model.trainable_variables))
                batch_info = {
                    "total_loss": task_loss,
                    "grad_norm_loss": tf.constant(0.0),
                    "task_weight": tf.constant(1.0),
                    "constraint_weight": tf.constant(0.0),
                }
            del tape

            epoch_task += float(task_loss.numpy())
            epoch_constraint += float(constraint_loss.numpy())
            epoch_total += float(batch_info["total_loss"].numpy())
            epoch_grad_norm += float(batch_info["grad_norm_loss"].numpy())
            epoch_task_w += float(batch_info["task_weight"].numpy())
            epoch_con_w += float(batch_info["constraint_weight"].numpy())
            n_batches += 1

        val_preds = model(X_val, training=False)
        val_loss = float(tf.reduce_mean(tf.square(val_preds - y_val)).numpy())

        objective_metric = (
            val_loss
            + objective_constraint_weight * (epoch_constraint / n_batches)
        )

        history["task_loss"].append(epoch_task / n_batches)
        history["constraint_loss"].append(epoch_constraint / n_batches)
        history["total_loss"].append(epoch_total / n_batches)
        history["val_loss"].append(val_loss)
        history["grad_norm_loss"].append(epoch_grad_norm / n_batches)
        history["objective_metric"].append(objective_metric)
        history["task_weight"].append(epoch_task_w / n_batches)
        history["constraint_weight"].append(epoch_con_w / n_batches)

        if trial is not None:
            trial.report(objective_metric, step=epoch)
            if trial.should_prune():
                import optuna
                raise optuna.TrialPruned()

        if verbose:
            phase_label = "" if constraint_active else " [task only]"
            print(
                f"Epoch {epoch + 1}/{epochs}{phase_label} — "
                f"task: {epoch_task / n_batches:.4f}, "
                f"safe: {epoch_constraint / n_batches:.4f}, "
                f"total: {epoch_total / n_batches:.4f}, "
                f"weights: ({epoch_task_w / n_batches:.3f}, "
                f"{epoch_con_w / n_batches:.3f}), "
                f"val: {val_loss:.4f}"
            )

    return history
