"""Neural network training, evaluation, and export."""

import os

import tensorflow as tf
from tensorflow.keras import models, layers
from sklearn.model_selection import train_test_split
from sklearn.preprocessing import StandardScaler
import idx2numpy

from . import constants as C


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

    The scaler is fit on the training split only to avoid data leakage.

    Returns (X_train, X_test, y_train, y_test, scaler).
    """
    y = y.reshape(-1, 1) if y.ndim == 1 else y

    X_train_raw, X_test_raw, y_train, y_test = train_test_split(
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
    import re

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
    os.makedirs("data", exist_ok=True)
    idx2numpy.convert_to_file("data/pk_mean.idx", scaler.mean_)
    idx2numpy.convert_to_file("data/pk_std.idx", scaler.scale_)


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
    parameters: dict[str, float],
    alpha=0.5,
    epochs=C.DEFAULT_EPOCHS,
    batch_size=C.DEFAULT_BATCH_SIZE,
    normalise_losses=False,
    phase_switch=0,
):
    """Train with combined task loss + a single Vehicle constraint loss.

    Uses a custom tf.GradientTape loop so that the Vehicle specification
    loss can be backpropagated alongside the standard MSE loss.

    Args:
        model: Keras model.
        X_train, y_train: Training data.
        X_val, y_val: Validation data.
        constraint_fn: Callable loss function for a single Vehicle property.
        parameters: Dictionary of parameters for the constraint function.
        alpha: Weight for task loss; (1-alpha) for constraint loss.
        epochs: Number of training epochs.
        batch_size: Batch size.
        normalise_losses: If True, divide each loss by its value at the first
            batch so both start at ~1.0, making alpha meaningful regardless
            of scale differences.
        phase_switch: If > 0, train on task loss only for this many epochs,
            then switch on constraint loss for the remainder. alpha is applied
            only during the constraint phase.

    Returns:
        dict with training history (task_loss, constraint_loss, total_loss per epoch).
    """
    optimizer = tf.keras.optimizers.Adam(clipnorm=1.0)
    dataset = tf.data.Dataset.from_tensor_slices((X_train, y_train))
    dataset = dataset.shuffle(len(X_train)).batch(batch_size)

    def network_fn(x):
        return tf.reshape(model(tf.reshape(x, [1, -1]), training=True), [-1])

    history = {"task_loss": [], "constraint_loss": [], "total_loss": [], "val_loss": []}

    task_loss_0 = None
    constraint_loss_0 = None

    for epoch in range(epochs):
        epoch_task, epoch_constraint, epoch_total, n_batches = 0.0, 0.0, 0.0, 0
        constraint_active = (phase_switch == 0) or (epoch >= phase_switch)

        for x_batch, y_batch in dataset:
            with tf.GradientTape() as tape:
                preds = model(x_batch, training=True)
                task_loss = tf.reduce_mean(tf.square(preds - y_batch))

                if constraint_active:
                    constraint_loss = constraint_fn(network_fn)

                    if normalise_losses:
                        if task_loss_0 is None:
                            task_loss_0 = float(task_loss.numpy()) or 1.0
                            constraint_loss_0 = float(constraint_loss.numpy()) or 1.0
                            print(f"Loss normalisation anchors — task: {task_loss_0:.4f}, constraint: {constraint_loss_0:.4f}")
                        normed_task = task_loss / task_loss_0
                        normed_constraint = constraint_loss / constraint_loss_0
                        total_loss = alpha * normed_task + (1 - alpha) * normed_constraint
                    else:
                        total_loss = alpha * task_loss + (1 - alpha) * constraint_loss
                else:
                    constraint_loss = tf.constant(0.0)
                    total_loss = task_loss

            grads = tape.gradient(total_loss, model.trainable_variables)
            grads = [tf.where(tf.math.is_finite(g), g, tf.zeros_like(g))
                     if g is not None else g for g in grads]
            optimizer.apply_gradients(zip(grads, model.trainable_variables))

            epoch_task += task_loss.numpy()
            epoch_constraint += constraint_loss.numpy()
            epoch_total += total_loss.numpy()
            n_batches += 1

        val_preds = model(X_val, training=False)
        val_loss = tf.reduce_mean(tf.square(val_preds - y_val)).numpy()

        history["task_loss"].append(epoch_task / n_batches)
        history["constraint_loss"].append(epoch_constraint / n_batches)
        history["total_loss"].append(epoch_total / n_batches)
        history["val_loss"].append(val_loss)

        phase_label = "" if constraint_active else " [task only]"
        print(
            f"Epoch {epoch + 1}/{epochs}{phase_label} — "
            f"task: {epoch_task / n_batches:.4f}, "
            f"constraint: {epoch_constraint / n_batches:.4f}, "
            f"total: {epoch_total / n_batches:.4f}, "
            f"val: {val_loss:.4f}"
        )

    return history
