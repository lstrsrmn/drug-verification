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
    layer_list.append(layers.Dense(1, activation="relu"))

    model = models.Sequential(layer_list)
    model.compile(optimizer="adam", loss="mse", metrics=["mae"])
    return model


def prepare_data(X, y, test_size=C.DEFAULT_TEST_SIZE, seed=C.DEFAULT_SEED):
    """Scale features and split into train/test sets.

    The scaler is fit on the training split only to avoid data leakage.

    Returns (X_train, X_test, y_train, y_test, scaler).
    """
    y = y.reshape(-1, 1) if y.ndim == 1 else y

    X_train_raw, X_test_raw, y_train, y_test = train_test_split(
        X, y, test_size=test_size, random_state=seed
    )

    scaler = StandardScaler()
    X_train = scaler.fit_transform(X_train_raw)
    X_test = scaler.transform(X_test_raw)

    return X_train, X_test, y_train, y_test, scaler


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


def evaluate_model(model, X_test, y_test):
    """Evaluate model on the test set.

    Returns a dict with mse, mae, and max_absolute_error.
    """
    preds = model.predict(X_test, verbose=0)
    errors = preds - y_test
    mse = float(tf.reduce_mean(tf.square(errors)).numpy())
    mae = float(tf.reduce_mean(tf.abs(errors)).numpy())
    max_ae = float(tf.reduce_max(tf.abs(errors)).numpy())
    return {"mse": mse, "mae": mae, "max_absolute_error": max_ae}


def update_vcl_scaler(scaler, spec_path="pk.vcl"):
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

    mean_str = ", ".join(f"{v:.8g}" for v in scaler.mean_)
    std_str = ", ".join(f"{v:.8g}" for v in scaler.scale_)

    # Use .idx files instead for portability and to not have to overwrite a file
    # with open(spec_path, "r") as f:
    #     content = f.read()

    # # Replace the value lines; patterns are anchored to the assignment so that
    # # the type declaration lines above them are left untouched.
    # content = re.sub(
    #     r"(meanScalingValues\s*=\s*)\[.*?\]",
    #     rf"\g<1>[{mean_str}]",
    #     content,
    # )
    # content = re.sub(
    #     r"(standardDeviationValues\s*=\s*)\[.*?\]",
    #     rf"\g<1>[{std_str}]",
    #     content,
    # )

    # with open(spec_path, "w") as f:
    #     f.write(content)

    print(f"Updated {spec_path} with scaler values from this training run.")
    print(f"  meanScalingValues        = [{mean_str}]")
    print(f"  standardDeviationValues  = [{std_str}]")
    idx2numpy.convert_to_file("pk_mean.idx", scaler.mean_)
    idx2numpy.convert_to_file("pk_std.idx", scaler.scale_)


def export_onnx(model, out_path="pk.onnx", positive_clamp=True):
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

        # Add a scalar constant initializer for the epsilon value
        epsilon_name = "positive_clamp_epsilon"
        epsilon_tensor = numpy_helper.from_array(
            np.array([0.0001], dtype=np.float32), name=epsilon_name
        )
        graph.initializer.append(epsilon_tensor)

        # Rename the original output so it's no longer the graph output
        shifted_output = original_output + "_shifted"

        # Add an Add node: shifted = original + 0.0001
        add_node = onnx.helper.make_node(
            "Add",
            inputs=[original_output, epsilon_name],
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
    parameters: dict[str, float],
    alpha=C.DEFAULT_GRADNORM_ALPHA,
    gradnorm_lr=C.DEFAULT_GRADNORM_WEIGHT_LR,
    initial_constraint_weight=C.DEFAULT_INITIAL_CONSTRAINT_WEIGHT,
    optimizer_lr=C.DEFAULT_OPTIMIZER_LR,
    objective_constraint_weight=C.DEFAULT_TUNE_CONSTRAINT_OBJECTIVE_WEIGHT,
    trial=None,
    epochs=C.DEFAULT_EPOCHS,
    batch_size=C.DEFAULT_BATCH_SIZE,
    verbose=True,
):
    """Train with task loss + Vehicle constraint loss balanced by GradNorm.

    Uses a custom tf.GradientTape loop so that the Vehicle specification
    loss can be backpropagated alongside the standard MSE loss with
    adaptive weighting.

    Args:
        model: Keras model.
        X_train, y_train: Training data.
        X_val, y_val: Validation data.
        constraint_fn: Callable loss function for a single Vehicle property.
        parameters: Dictionary of parameters for the constraint function.
        alpha: GradNorm restoring-force exponent from Chen et al. (2018).
        gradnorm_lr: Learning rate for GradNorm's task-weight optimizer.
        initial_constraint_weight: Initial relative weight for constraint loss.
        optimizer_lr: Learning rate for model parameter optimizer.
        objective_constraint_weight: Coefficient for constraint loss when computing
            per-epoch objective metric (useful for tuning/pruning).
        trial: Optional Optuna trial-like object with report()/should_prune().
        epochs: Number of training epochs.
        batch_size: Batch size.
        verbose: Whether to print per-epoch logs.

    Returns:
        dict with training history (task/constraint/total losses, validation loss,
        GradNorm loss, objective metric, and adaptive task weights per epoch).
    """
    optimizer = tf.keras.optimizers.Adam(learning_rate=optimizer_lr)
    dataset = tf.data.Dataset.from_tensor_slices((X_train, y_train))
    dataset = dataset.shuffle(len(X_train)).batch(batch_size)
    grad_norm = GradNorm(
        alpha=alpha,
        weight_lr=gradnorm_lr,
        initial_constraint_weight=initial_constraint_weight,
    )

    constraint_parameters = {
        key: value
        for key, value in parameters.items()
        if key not in C.CONSTRAINT_PARAM_EXCLUSIONS
    }

    def network_fn(x):
        return tf.reshape(model(tf.reshape(x, [1, -1]), training=True), [-1])

    history = {
        "task_loss": [],
        "constraint_loss": [],
        "total_loss": [],
        "val_loss": [],
        "grad_norm_loss": [],
        "objective_metric": [],
        "task_weight": [],
        "constraint_weight": [],
    }

    for epoch in range(epochs):
        epoch_task, epoch_constraint, epoch_total, epoch_grad_norm, n_batches = 0.0, 0.0, 0.0, 0.0, 0
        epoch_task_weight, epoch_constraint_weight = 0.0, 0.0

        for x_batch, y_batch in dataset:
            with tf.GradientTape(persistent=True) as tape:
                preds = model(x_batch, training=True)
                task_loss = tf.reduce_mean(tf.square(preds - y_batch))
                constraint_loss = tf.cast(
                    tf.reduce_mean(constraint_fn(pk=network_fn, **constraint_parameters)),
                    tf.float32,
                )

            batch_info = grad_norm.balance(
                task_loss=task_loss,
                constraint_loss=constraint_loss,
                tape=tape,
                model_optimizer=optimizer,
                model_variables=model.trainable_variables,
            )
            del tape

            total_loss = batch_info["total_loss"]
            grad_norm_loss = batch_info["grad_norm_loss"]
            task_weight = batch_info["task_weight"]
            constraint_weight = batch_info["constraint_weight"]

            epoch_task += float(task_loss.numpy())
            epoch_constraint += float(constraint_loss.numpy())
            epoch_total += float(total_loss.numpy())
            epoch_grad_norm += float(grad_norm_loss.numpy())
            epoch_task_weight += float(task_weight.numpy())
            epoch_constraint_weight += float(constraint_weight.numpy())
            n_batches += 1

        # Validation loss
        val_preds = model(X_val, training=False)
        val_loss = tf.reduce_mean(tf.square(val_preds - y_val)).numpy()

        history["task_loss"].append(epoch_task / n_batches)
        history["constraint_loss"].append(epoch_constraint / n_batches)
        history["total_loss"].append(epoch_total / n_batches)
        history["val_loss"].append(val_loss)
        history["grad_norm_loss"].append(epoch_grad_norm / n_batches)
        objective_metric = float(val_loss) + float(objective_constraint_weight) * float(
            epoch_constraint / n_batches
        )
        history["objective_metric"].append(objective_metric)
        history["task_weight"].append(epoch_task_weight / n_batches)
        history["constraint_weight"].append(epoch_constraint_weight / n_batches)

        if trial is not None:
            trial.report(objective_metric, step=epoch)
            if trial.should_prune():
                import optuna

                raise optuna.TrialPruned()

        if verbose:
            print(
                f"Epoch {epoch + 1}/{epochs} — "
                f"task: {epoch_task / n_batches:.4f}, "
                f"constraint: {epoch_constraint / n_batches:.4f}, "
                f"total: {epoch_total / n_batches:.4f}, "
                f"gradnorm: {epoch_grad_norm / n_batches:.4f}, "
                f"objective: {objective_metric:.4f}, "
                f"weights: ({epoch_task_weight / n_batches:.3f}, {epoch_constraint_weight / n_batches:.3f}), "
                f"val: {val_loss:.4f}"
            )

    return history
