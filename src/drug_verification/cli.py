"""Command-line interface for the drug verification pipeline."""

import argparse

from drug_verification import constants as C
from drug_verification import test_utils
from drug_verification.vehicle_loss import load_drug_verification_constraints



def cmd_simulate(args):
    """Run PK/PD simulation and save data to CSV."""
    from drug_verification.simulation import simulate_cohort
    from drug_verification.types import SimulationConfig
    from drug_verification.io import save_data

    cfg = SimulationConfig(
        num_patients=args.num_patients,
        timesteps=args.timesteps,
        seed=args.seed,
    )
    print(f"Simulating {cfg.num_patients} patients, {cfg.timesteps} timesteps...")
    X, y = simulate_cohort(cfg, seed=args.seed)
    save_data(X, y, x_path=args.x_out, y_path=args.y_out)


def cmd_train(args):
    """Simulate data, train the neural network, and optionally save the model."""
    import tensorflow as tf

    from drug_verification.simulation import simulate_cohort
    from drug_verification.types import SimulationConfig
    from drug_verification.training import build_model, prepare_data, train_model, train_model_with_constraint, evaluate_model, update_vcl_scaler
    from drug_verification.io import save_data

    tf.random.set_seed(args.seed)

    cfg = SimulationConfig(
        num_patients=args.num_patients,
        timesteps=args.timesteps,
        seed=args.seed,
    )
    print(f"Simulating {cfg.num_patients} patients...")
    X, y = simulate_cohort(cfg, seed=args.seed)
    save_data(X, y)

    X_train, X_test, y_train, y_test, scaler, y_scaler = prepare_data(X, y, seed=args.seed)
    print(f"Scaler mean: {scaler.mean_}")
    print(f"Scaler std:  {scaler.scale_}")

    # Keep the Vehicle spec in sync with the fitted scaler.
    # The spec hardcodes normalisation constants used during verification — if
    # these differ from what the trained model sees, the proof is unsound.
    update_vcl_scaler(scaler, y_scaler=y_scaler, spec_path=args.spec_path)

    model = build_model(X_train.shape[1])
    model.summary()

    if args.vehicle_loss:
        # Build parameters from defaults, overridden by any CLI --param flags
        parameters = dict(C.DEFAULT_SPEC_PARAMS)
        if args.params:
            for kv in args.params:
                key, value = kv.split(":", 1)
                parameters[key] = float(value)
        constraint_fns = load_drug_verification_constraints(
            spec_path=args.spec_path,
            properties=["safeFar", "safeNear"],
            mean=scaler.mean_,
            std_dev=scaler.scale_,
            parameters=parameters,
        )
        print(f"Training with Vehicle properties: {list(constraint_fns.keys())}")

        history = train_model_with_constraint(
            model, X_train, y_train, X_test, y_test,
            constraint_fn=constraint_fns["safeFar"],
            constraint2_fn=constraint_fns["safeNear"],
            y_mean=float(y_scaler.mean_[0]),
            y_std=float(y_scaler.scale_[0]),
            alpha=args.alpha,
            epochs=args.epochs,
            batch_size=args.batch_size,
            phase_switch=args.phase_switch,
        )
    else:
        history = train_model(
            model, X_train, y_train, X_test, y_test,
            epochs=args.epochs,
            batch_size=args.batch_size,
        )

    metrics = evaluate_model(model, X_test, y_test, y_scaler=y_scaler)
    print(f"\nTest evaluation:")
    print(f"  MSE:              {metrics['mse']:.4f}")
    print(f"  MAE:              {metrics['mae']:.4f}")
    print(f"  Max absolute err: {metrics['max_absolute_error']:.4f}")

    if args.save_model:
        model.save(args.save_model)
        print(f"Saved Keras model to {args.save_model}")


def cmd_plot(args):
    """Load saved data and generate plots."""
    from drug_verification.io import load_data
    from drug_verification.plotting import plot_patient_trajectories

    X, y = load_data(args.x_in, args.y_in)
    num_patients = len(X) // (C.TIMESTEPS - 1)
    save_dir = args.output_dir if args.no_show else None
    plot_patient_trajectories(X, y, num_patients, save_dir=save_dir)

    if args.no_show and args.output_dir:
        print(f"Plots saved to {args.output_dir}/")


def cmd_export(args):
    """Export a saved Keras model to ONNX."""
    import tensorflow as tf
    from drug_verification.training import export_onnx

    model = tf.keras.models.load_model(args.model_path)
    export_onnx(model, out_path=args.onnx_out)


def cmd_test(args):
    """Build and export a zero-weight ONNX model for formal verification."""
    print(f"Building zero-weight model with input size {args.input_size}...")
    output_path = test_utils.build_it(args.input_size, args.output_path)
    print(f"✓ Model exported to {output_path}")

    if args.validate:
        try:
            print(f"Validating model with onnxruntime...")
            test_utils.print_it(
                [0.0] * args.input_size,
                model_path=output_path
            )
            print(f"✓ Model validation successful")
        except ImportError:
            print(f"⚠ onnxruntime not installed; skipping validation")
        except Exception as e:
            print(f"✗ Validation failed: {e}")


def cmd_tune(args):
    """Run Optuna hyperparameter tuning for constrained training."""
    from drug_verification.tuning import run_vehicle_loss_study

    result = run_vehicle_loss_study(args)
    summary = result["summary"]
    print("\nTuning complete.")
    print(f"  Study:        {summary['study_name']}")
    print(f"  Best trial:   {summary['best_trial_number']}")
    print(f"  Best value:   {summary['best_value']:.6f}")
    print(f"  Params saved: {result['best_params_path']}")
    print(f"  Trials CSV:   {result['trials_csv_path']}")


def cmd_all(args):
    """Run the full pipeline: simulate → train → export → plot."""
    # Simulate
    args.x_out = "patient_states.csv"
    args.y_out = "dose_targets.csv"
    cmd_simulate(args)

    # Train — always enable Vehicle constraint loss in the full pipeline
    args.vehicle_loss = True
    args.save_model = args.save_model or "pk_model.keras"
    cmd_train(args)

    # Export
    args.model_path = args.save_model
    args.onnx_out = args.onnx_out if hasattr(args, "onnx_out") else "models/pk.onnx"
    cmd_export(args)

    # Plot
    args.x_in = "patient_states.csv"
    args.y_in = "dose_targets.csv"
    cmd_plot(args)


def build_parser():
    parser = argparse.ArgumentParser(
        prog="pk",
        description="PK/PD simulation, NN training, and formal verification pipeline.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    # --- Common arguments ---
    def add_common(p):
        p.add_argument("--seed", type=int, default=C.DEFAULT_SEED, help="Random seed")
        p.add_argument("--num-patients", type=int, default=C.NUM_PATIENTS)
        p.add_argument("--timesteps", type=int, default=C.TIMESTEPS)

    def add_train_args(p):
        p.add_argument("--epochs", type=int, default=C.DEFAULT_EPOCHS)
        p.add_argument("--batch-size", type=int, default=C.DEFAULT_BATCH_SIZE)
        p.add_argument("--save-model", type=str, default=None, help="Path to save Keras model")
        p.add_argument("--vehicle-loss", action="store_true", help="Enable Vehicle spec constraint loss")
        p.add_argument("--property", type=str, default="safeFar", help="Vehicle property to train against (default: safeFar)")
        p.add_argument("--alpha", type=float, default=C.DEFAULT_GRADNORM_ALPHA, help="GradNorm restoring-force exponent")
        p.add_argument("--phase-switch", type=int, default=0, metavar="EPOCH",
                       help="Train on task loss only until EPOCH, then switch on GradNorm constraints. 0 = constraints active from epoch 1.")
        p.add_argument("--spec-path", type=str, default="pk.vcl", help="Path to Vehicle spec file")
        p.add_argument("-p", "--param", dest="params", action="append", metavar="KEY:VALUE",
                       help="Override a Vehicle parameter (e.g. -p Ka:4.5). Can be repeated.")

    # simulate
    p_sim = sub.add_parser("simulate", help="Run PK/PD simulation and save CSVs")
    add_common(p_sim)
    p_sim.add_argument("--x-out", default="patient_states.csv")
    p_sim.add_argument("--y-out", default="dose_targets.csv")

    # train
    p_train = sub.add_parser("train", help="Simulate + train neural network")
    add_common(p_train)
    add_train_args(p_train)

    # plot
    p_plot = sub.add_parser("plot", help="Generate plots from saved data")
    p_plot.add_argument("--x-in", default="patient_states.csv")
    p_plot.add_argument("--y-in", default="dose_targets.csv")
    p_plot.add_argument("--output-dir", default="nn_plots", help="Directory to save plots")
    p_plot.add_argument("--no-show", action="store_true", help="Save plots without displaying")

    # export
    p_export = sub.add_parser("export", help="Export Keras model to ONNX")
    p_export.add_argument("--model-path", required=True, help="Path to saved Keras model")
    p_export.add_argument("--onnx-out", default="models/pk.onnx")

    # all
    p_all = sub.add_parser("all", help="Full pipeline: simulate → train → export → plot")
    add_common(p_all)
    add_train_args(p_all)
    p_all.add_argument("--output-dir", default="nn_plots")
    p_all.add_argument("--no-show", action="store_true")
    p_all.add_argument("--onnx-out", default="models/pk.onnx")

    # test
    p_test = sub.add_parser("test", help="Build zero-weight ONNX model for formal verification")
    p_test.add_argument("--input-size", type=int, default=5, help="Input dimension for the model (default: 5)")
    p_test.add_argument("--output-path", default="pk.onnx", help="Path where ONNX model will be saved (default: pk.onnx)")
    p_test.add_argument("--validate", action="store_true", help="Validate generated model with onnxruntime")

    # tune
    p_tune = sub.add_parser("tune", help="Run Optuna tuning for Vehicle-loss constrained training")
    add_common(p_tune)
    p_tune.add_argument("--epochs", type=int, default=C.DEFAULT_EPOCHS)
    p_tune.add_argument("--spec-path", type=str, default="pk.vcl")
    p_tune.add_argument("-p", "--param", dest="params", action="append", metavar="KEY:VALUE")
    p_tune.add_argument("--n-trials", type=int, default=C.DEFAULT_OPTUNA_N_TRIALS)
    p_tune.add_argument("--timeout", type=int, default=C.DEFAULT_OPTUNA_TIMEOUT_SECONDS)
    p_tune.add_argument("--storage", type=str, default=C.DEFAULT_OPTUNA_STORAGE)
    p_tune.add_argument("--study-name", type=str, default=C.DEFAULT_OPTUNA_STUDY_NAME)
    p_tune.add_argument("--pruner", choices=["median", "hyperband", "none"], default=C.DEFAULT_OPTUNA_PRUNER)
    p_tune.add_argument("--objective-constraint-weight", type=float, default=C.DEFAULT_TUNE_CONSTRAINT_OBJECTIVE_WEIGHT)
    p_tune.add_argument("--best-params-out", type=str, default="optuna_best_params.json")
    p_tune.add_argument("--trials-csv-out", type=str, default="optuna_trials.csv")

    return parser


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)

    commands = {
        "simulate": cmd_simulate,
        "train": cmd_train,
        "plot": cmd_plot,
        "export": cmd_export,
        "test": cmd_test,
        "all": cmd_all,
        "tune": cmd_tune,
    }
    commands[args.command](args)


if __name__ == "__main__":
    main()
