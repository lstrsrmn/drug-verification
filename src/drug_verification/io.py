"""I/O helpers for saving and loading simulation data."""

import os

import numpy as np
import pandas as pd


def save_data(X, y, x_path="data/patient_states.csv", y_path="data/dose_targets.csv"):
    """Save simulation state/action arrays to CSV files."""
    df_X = pd.DataFrame(X, columns=["C", "T", "WBC", "Age", "Weight"])
    df_y = pd.DataFrame(y, columns=["Dose"])
    df_X.to_csv(x_path, index=False)
    df_y.to_csv(y_path, index=False)
    print(f"Saved {x_path} ({len(df_X)} rows) and {y_path}")


def load_data(x_path="data/patient_states.csv", y_path="data/dose_targets.csv"):
    """Load simulation data from CSV files."""
    df_X = pd.read_csv(x_path)
    df_y = pd.read_csv(y_path)
    return df_X.values.astype(np.float32), df_y.values.flatten().astype(np.float32)


def save_idx(X, y, x_path="X_vehicle.idx", y_path="y_vehicle.idx"):
    """Save raw arrays in IDX format (for Vehicle / verification tools)."""
    import idx2numpy

    idx2numpy.convert_to_file(x_path, X.astype(np.float32))
    idx2numpy.convert_to_file(y_path, y.astype(np.float32))
    print(f"Saved {x_path} and {y_path}")
