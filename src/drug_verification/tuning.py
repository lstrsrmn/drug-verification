"""Hyperparameter tuning utilities for constrained (Vehicle-loss) training.

This module intentionally keeps the tuning workflow compact and reproducible,
which suits short-lived research repositories.
"""

from __future__ import annotations

import json
from pathlib import Path

import tensorflow as tf

from . import constants as C
from .simulation import simulate_cohort
from .training import build_model, prepare_data, train_model_with_constraint, update_vcl_scaler
from .types import SimulationConfig
from .vehicle_loss import load_drug_verification_constraints


def _parse_param_overrides(param_items: list[str] | None) -> dict[str, float]:
    """Parse repeated KEY:VALUE overrides from CLI."""
    overrides: dict[str, float] = {}
    if not param_items:
        return overrides

    for item in param_items:
        key, value = item.split(":", 1)
        overrides[key] = float(value)
    return overrides


def _create_pruner(optuna_module, pruner_name: str):
    """Create a small set of robust pruner options."""
    if pruner_name == "median":
        return optuna_module.pruners.MedianPruner(n_startup_trials=5, n_warmup_steps=5)
    if pruner_name == "hyperband":
        return optuna_module.pruners.HyperbandPruner()
    if pruner_name == "none":
        return optuna_module.pruners.NopPruner()
    raise ValueError(f"Unsupported pruner: {pruner_name}")


def _suggest_hidden_sizes(trial, min_layers: int, max_layers: int) -> tuple[int, ...]:
    """Suggest a compact MLP shape for this task."""
    n_layers = trial.suggest_int("n_layers", min_layers, max_layers)
    return tuple(
        trial.suggest_int(f"units_l{i}", C.TUNE_UNITS_RANGE[0], C.TUNE_UNITS_RANGE[1], log=True)
        for i in range(n_layers)
    )


def run_vehicle_loss_study(args) -> dict[str, object]:
    """Run an Optuna study for Vehicle-loss constrained training."""
    try:
        import optuna
    except ImportError as exc:
        raise RuntimeError(
            "Optuna is required for `pk tune`. Install with `pip install optuna`."
        ) from exc

    tf.keras.utils.set_random_seed(args.seed)

    cfg = SimulationConfig(
        num_patients=args.num_patients,
        timesteps=args.timesteps,
        seed=args.seed,
    )
    X, y = simulate_cohort(cfg, seed=args.seed)
    X_train, X_val, y_train, y_val, scaler = prepare_data(X, y, seed=args.seed)

    # Keep verification normalisation aligned with tuned runs.
    update_vcl_scaler(scaler, spec_path=args.spec_path)

    parameters = dict(C.DEFAULT_SPEC_PARAMS)
    parameters.update(_parse_param_overrides(args.params))
    parameters["mean"] = scaler.mean_
    parameters["std_dev"] = scaler.scale_

    constraint_fns = load_drug_verification_constraints(
        spec_path=args.spec_path,
        properties=[args.property],
    )
    constraint_fn = constraint_fns[args.property]

    sampler = optuna.samplers.TPESampler(seed=args.seed)
    pruner = _create_pruner(optuna, args.pruner)

    study = optuna.create_study(
        direction="minimize",
        sampler=sampler,
        pruner=pruner,
        storage=args.storage,
        study_name=args.study_name,
        load_if_exists=True,
    )

    def objective(trial):
        tf.keras.backend.clear_session()
        tf.keras.utils.set_random_seed(args.seed)

        hidden_sizes = _suggest_hidden_sizes(
            trial, C.TUNE_N_LAYERS_RANGE[0], C.TUNE_N_LAYERS_RANGE[1]
        )
        learning_rate = trial.suggest_float(
            "learning_rate",
            C.TUNE_LEARNING_RATE_RANGE[0],
            C.TUNE_LEARNING_RATE_RANGE[1],
            log=True,
        )
        batch_size = trial.suggest_categorical(
            "batch_size", list(C.TUNE_BATCH_SIZE_CHOICES)
        )
        gradnorm_alpha = trial.suggest_float(
            "gradnorm_alpha",
            C.TUNE_GRADNORM_ALPHA_RANGE[0],
            C.TUNE_GRADNORM_ALPHA_RANGE[1],
        )
        gradnorm_weight_lr = trial.suggest_float(
            "gradnorm_weight_lr",
            C.TUNE_GRADNORM_WEIGHT_LR_RANGE[0],
            C.TUNE_GRADNORM_WEIGHT_LR_RANGE[1],
            log=True,
        )
        initial_constraint_weight = trial.suggest_float(
            "initial_constraint_weight",
            C.TUNE_INITIAL_CONSTRAINT_WEIGHT_RANGE[0],
            C.TUNE_INITIAL_CONSTRAINT_WEIGHT_RANGE[1],
        )

        model = build_model(X_train.shape[1], hidden_sizes=hidden_sizes)
        history = train_model_with_constraint(
            model=model,
            X_train=X_train,
            y_train=y_train,
            X_val=X_val,
            y_val=y_val,
            constraint_fn=constraint_fn,
            parameters=parameters,
            alpha=gradnorm_alpha,
            gradnorm_lr=gradnorm_weight_lr,
            initial_constraint_weight=initial_constraint_weight,
            optimizer_lr=learning_rate,
            objective_constraint_weight=args.objective_constraint_weight,
            trial=trial,
            epochs=args.epochs,
            batch_size=batch_size,
            verbose=False,
        )

        objective_metric = float(history["objective_metric"][-1])
        trial.set_user_attr("final_val_loss", float(history["val_loss"][-1]))
        trial.set_user_attr("final_constraint_loss", float(history["constraint_loss"][-1]))
        trial.set_user_attr("hidden_sizes", list(hidden_sizes))
        return objective_metric

    study.optimize(
        objective,
        n_trials=args.n_trials,
        timeout=args.timeout,
        gc_after_trial=True,
    )

    best = study.best_trial
    summary: dict[str, object] = {
        "study_name": study.study_name,
        "best_trial_number": int(best.number),
        "best_value": float(best.value),
        "best_params": best.params,
    }

    best_params_path = Path(args.best_params_out)
    best_params_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")

    trials_df = study.trials_dataframe(attrs=("number", "value", "params", "state"))
    trials_df.to_csv(args.trials_csv_out, index=False)

    return {
        "summary": summary,
        "best_params_path": str(best_params_path),
        "trials_csv_path": args.trials_csv_out,
    }
