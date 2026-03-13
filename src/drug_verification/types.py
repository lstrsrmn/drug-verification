"""Data structures for the PK/PD simulation."""

from dataclasses import dataclass

import numpy as np


@dataclass
class PatientCovariates:
    """Demographics and baseline characteristics for a single patient."""
    age: int
    weight: float
    sex: int  # 0=male, 1=female


@dataclass
class SimulationConfig:
    """Grouped simulation parameters (allows overriding defaults)."""
    timesteps: int = 48
    dt: float = 0.5
    num_patients: int = 50
    seed: int = 42

    # Baseline PK/PD
    ke: float = 0.1
    Vd: float = 30.0
    b_temp: float = 0.005
    c_wbc: float = 0.02
    a_temp_inf: float = 0.05
    a_wbc_inf: float = 0.1
    k_inf_T: float = 0.08
    k_home_T: float = 0.12
    k_inf_W: float = 0.12
    k_home_W: float = 0.04

    # Normal ranges
    T_norm: tuple = (36.0, 38.0)
    WBC_norm: tuple = (4.0, 12.0)
    C_max: float = 30.0

    # Dose bounds
    D_min: float = 0.0
    D_max: float = 1500.0


@dataclass
class EffectiveParams:
    """Patient-specific effective PK/PD parameters after covariate adjustment."""
    ke_eff: float
    Vd_eff: float
    a_temp_inf_eff: float
    a_wbc_inf_eff: float
    T_set: float
    WBC_set: float
    k_inf_T_eff: float
    k_home_T_eff: float
    k_inf_W_eff: float
    k_home_W_eff: float
