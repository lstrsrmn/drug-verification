"""Plotting utilities for patient trajectories and model evaluation."""

import os

import matplotlib.pyplot as plt

from . import constants as C


def plot_patient_trajectories(
    X, y, num_patients, patient_indices=None, save_dir=None
):
    """Plot temperature, WBC, concentration, and dose for selected patients.

    Args:
        X: Feature array, shape (total_samples, 5).
        y: Dose array, shape (total_samples,).
        num_patients: Total number of patients in the dataset.
        patient_indices: Which patients to plot (default: first 5).
        save_dir: If provided, save plots here instead of showing.
    """
    samples_per_patient = C.TIMESTEPS - 1
    X_reshaped = X.reshape(num_patients, samples_per_patient, -1)
    y_reshaped = y.reshape(num_patients, samples_per_patient)

    if patient_indices is None:
        patient_indices = range(min(5, num_patients))

    for p in patient_indices:
        fig, axes = plt.subplots(1, 4, figsize=(16, 4))

        axes[0].plot(X_reshaped[p, :, 1], label="Temp")
        axes[0].axhline(C.T_NORM[0], color="g", linestyle="--")
        axes[0].axhline(C.T_NORM[1], color="r", linestyle="--")
        axes[0].set_title(f"Patient {p + 1} Temperature")
        axes[0].legend()

        axes[1].plot(X_reshaped[p, :, 2], label="WBC")
        axes[1].axhline(C.WBC_NORM[0], color="g", linestyle="--")
        axes[1].axhline(C.WBC_NORM[1], color="r", linestyle="--")
        axes[1].set_title(f"Patient {p + 1} WBC")
        axes[1].legend()

        axes[2].plot(X_reshaped[p, :, 0], label="Drug Conc (C)")
        axes[2].axhline(C.C_MAX, color="r", linestyle="--", label="C_max")
        axes[2].set_title(f"Patient {p + 1} Drug Concentration")
        axes[2].legend()

        axes[3].plot(y_reshaped[p, :], label="Dose")
        axes[3].set_title(f"Patient {p + 1} Dose")
        axes[3].legend()

        fig.tight_layout()

        if save_dir:
            os.makedirs(save_dir, exist_ok=True)
            fig.savefig(os.path.join(save_dir, f"patient_{p + 1}_trajectory.png"))
            plt.close(fig)
        else:
            plt.show()


def plot_true_vs_predicted(y_true, y_pred, save_path=None):
    """Scatter plot of true vs predicted doses."""
    fig, ax = plt.subplots(figsize=(6, 6))
    ax.scatter(y_true, y_pred, alpha=0.5)
    ax.set_xlabel("True Dose")
    ax.set_ylabel("Predicted Dose")
    ax.set_title("NN Controller: True vs Predicted Dose")
    ax.plot([0, C.D_MAX], [0, C.D_MAX], "r--", label="Ideal x=y")
    ax.legend()
    fig.tight_layout()

    if save_path:
        os.makedirs(os.path.dirname(save_path) or ".", exist_ok=True)
        fig.savefig(save_path)
        plt.close(fig)
        print(f"Saved plot to {save_path}")
    else:
        plt.show()


def plot_training_history(history, save_path=None):
    """Plot training and validation loss/MAE curves."""
    fig, axes = plt.subplots(1, 2, figsize=(12, 4))

    axes[0].plot(history.history["loss"], label="Train Loss")
    axes[0].plot(history.history["val_loss"], label="Val Loss")
    axes[0].set_xlabel("Epoch")
    axes[0].set_ylabel("MSE Loss")
    axes[0].set_title("Loss")
    axes[0].legend()

    axes[1].plot(history.history["mae"], label="Train MAE")
    axes[1].plot(history.history["val_mae"], label="Val MAE")
    axes[1].set_xlabel("Epoch")
    axes[1].set_ylabel("MAE")
    axes[1].set_title("Mean Absolute Error")
    axes[1].legend()

    fig.tight_layout()

    if save_path:
        os.makedirs(os.path.dirname(save_path) or ".", exist_ok=True)
        fig.savefig(save_path)
        plt.close(fig)
        print(f"Saved plot to {save_path}")
    else:
        plt.show()
