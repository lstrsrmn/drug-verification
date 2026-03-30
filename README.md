This repository is for training and verifiyng a neural network controller for an antibiotic dispenser.

## Drug verification CLI

This repository exposes a single supported CLI entrypoint: `pk`.

### Install

Use your preferred workflow:

- `uv sync`
- or `pip install -e .`

If you do not have uv installed and want to try it out, follow [these instructions](https://docs.astral.sh/uv/getting-started/installation/).

### Usage

- `pk --help`
- `pk simulate --help`
- `pk train --help`
- `pk export --help`
- `pk plot --help`
- `pk all --help`
- `pk test --help`
- `pk tune --help`

When `pk train --vehicle-loss` is enabled, training uses GradNorm
for adaptive balancing between task and specification losses. The
`--alpha` argument corresponds to GradNorm's asymmetry hyperparameter.

### Quick tuning workflow (research-friendly)

Use `pk tune` to run Optuna over the most important hyperparameters (learning rate, batch size, hidden-layer shape, and GradNorm
weights).

Example:

- `pk tune --n-trials 25 --timeout 1800 --study-name vehicle_loss_hpo`

By default, studies are persisted to a local SQLite file (`optuna_vehicle.db`) so
you can stop and resume later with the same `--study-name`.

Outputs:

- `optuna_best_params.json` (best trial summary + parameters)
- `optuna_trials.csv` (all trial values, states, and parameter columns)

`python -m drug_verification` is intentionally not supported.
