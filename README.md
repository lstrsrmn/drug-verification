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

`python -m drug_verification` is intentionally not supported.
