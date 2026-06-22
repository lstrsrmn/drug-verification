"""GradNorm loss balancing for constrained training.

Paper: GradNorm: Gradient Normalization for Adaptive Loss Balancing in Deep
Multitask Networks (Chen et al., ICML 2018).
"""

from __future__ import annotations

import tensorflow as tf


def _global_l2_norm(grads: list[tf.Tensor | None]) -> tf.Tensor:
    """Compute an L2 norm across a list of gradient tensors."""
    squared_norms = [tf.reduce_sum(tf.square(g)) for g in grads if g is not None]
    if not squared_norms:
        return tf.constant(0.0, dtype=tf.float32)
    return tf.sqrt(tf.add_n(squared_norms))


class GradNorm:
    """Gradient normalization for two-task training (task + constraint).

    Balances task loss and constraint loss by adapting weights online
    according to the GradNorm objective (Chen et al., ICML 2018).
    """

    def __init__(
        self,
        alpha: float,
        weight_lr: float,
        initial_constraint_weight: float = 1.0,
        epsilon: float = 1e-8,
        min_weight: float = 0.05,
    ):
        self.n_tasks = 2
        self.alpha = tf.constant(alpha, dtype=tf.float32)
        self.epsilon = tf.constant(epsilon, dtype=tf.float32)
        self.min_weight = tf.constant(min_weight, dtype=tf.float32)
        self.normalised_initial_losses: tf.Tensor | None = None
        self.initial_losses: tf.Tensor | None = None

        initial_task_weight = float(self.n_tasks) - float(initial_constraint_weight)
        init = tf.constant(
            [initial_task_weight, float(initial_constraint_weight)],
            dtype=tf.float32,
        )
        init = self._renormalised_weights(init)

        self.weights = tf.Variable(init, trainable=True, name="gradnorm_weights")
        self.optimizer = tf.keras.optimizers.Adam(learning_rate=weight_lr)

    def _renormalised_weights(self, weights: tf.Tensor) -> tf.Tensor:
        """Project weights to positive values summing to the number of tasks."""
        clamped = tf.maximum(weights, self.min_weight)
        scale = tf.cast(self.n_tasks, tf.float32) / (
            tf.reduce_sum(clamped) + self.epsilon
        )
        return clamped * scale

    def renormalise(self) -> None:
        """Renormalise in-place so that sum(weights) == n_tasks."""
        self.weights.assign(self._renormalised_weights(self.weights))

    def _apply_gradients(
        self,
        optimizer: tf.keras.optimizers.Optimizer,
        grads: list[tf.Tensor | None],
        variables: list[tf.Variable],
    ) -> None:
        pairs = [(g, v) for g, v in zip(grads, variables, strict=False) if g is not None]
        if pairs:
            optimizer.apply_gradients(pairs)

    def balance(
        self,
        task_loss: tf.Tensor,
        constraint_loss: tf.Tensor,
        tape: tf.GradientTape,
        model_optimizer: tf.keras.optimizers.Optimizer,
        model_variables: list[tf.Variable],
    ) -> dict[str, tf.Tensor]:
        """Apply one GradNorm balancing step.

        Args:
            task_loss: MSE prediction objective.
            constraint_loss: Vehicle safe property loss.
            tape: Persistent gradient tape that recorded both losses.
            model_optimizer: Optimizer for model parameters.
            model_variables: Trainable model parameters.

        Returns:
            Dictionary with total_loss, grad_norm_loss, and per-task weights.
        """
        losses = tf.stack([
            tf.cast(task_loss, tf.float32),
            tf.cast(constraint_loss, tf.float32),
        ])

        if self.initial_losses is None:
            safe_initial = tf.where(
                losses <= self.epsilon,
                tf.fill(tf.shape(losses), self.epsilon),
                losses,
            )
            self.initial_losses = tf.stop_gradient(safe_initial)

        # Normalise each loss by its initial value so both start at ~1.0.
        normalised_losses = losses / (self.initial_losses + self.epsilon)

        weighted_losses = self.weights * normalised_losses
        total_loss = tf.reduce_sum(weighted_losses)

        # Compute per-loss gradients via the tape, then normalise by initial loss.
        raw_task_grads       = tape.gradient(task_loss,       model_variables)
        raw_constraint_grads = tape.gradient(constraint_loss, model_variables)

        t0 = self.initial_losses[0] + self.epsilon
        t1 = self.initial_losses[1] + self.epsilon
        w0, w1 = self.weights[0], self.weights[1]

        model_grads = []
        for g0, g1, var in zip(raw_task_grads, raw_constraint_grads, model_variables):
            g0 = g0 if g0 is not None else tf.zeros_like(var)
            g1 = g1 if g1 is not None else tf.zeros_like(var)
            model_grads.append(w0 * g0 / t0 + w1 * g1 / t1)

        self._apply_gradients(model_optimizer, model_grads, model_variables)

        task_grads       = [g / t0 if g is not None else None for g in raw_task_grads]
        constraint_grads = [g / t1 if g is not None else None for g in raw_constraint_grads]

        base_norms = tf.stack([
            _global_l2_norm(task_grads),
            _global_l2_norm(constraint_grads),
        ])
        base_norms = tf.stop_gradient(base_norms)

        loss_ratio = tf.stop_gradient(losses / (self.initial_losses + self.epsilon))
        inverse_train_rate = loss_ratio / (tf.reduce_mean(loss_ratio) + self.epsilon)

        with tf.GradientTape() as weight_tape:
            norms = self.weights * base_norms
            mean_norm = tf.reduce_mean(norms)
            target_norms = tf.stop_gradient(
                mean_norm * tf.pow(inverse_train_rate, self.alpha)
            )
            grad_norm_loss = tf.reduce_sum(tf.abs(norms - target_norms))

        weight_grads = weight_tape.gradient(grad_norm_loss, [self.weights])[0]
        if weight_grads is None:
            weight_grads = tf.zeros_like(self.weights)
        self.optimizer.apply_gradients([(weight_grads, self.weights)])
        self.renormalise()

        finite_weights = tf.where(
            tf.math.is_finite(self.weights),
            self.weights,
            tf.ones_like(self.weights),
        )
        self.weights.assign(self._renormalised_weights(finite_weights))

        return {
            "total_loss": total_loss,
            "grad_norm_loss": grad_norm_loss,
            "task_weight": self.weights[0],
            "constraint_weight": self.weights[1],
        }
