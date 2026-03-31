"""PK/PD patient simulation — generates state-action training data."""

import numpy as np
import math

from .types import PatientCovariates, EffectiveParams, SimulationConfig
from . import constants as C


def generate_patient_covariates(rng: np.random.RandomState) -> PatientCovariates:
    """Sample random patient demographics."""
    return PatientCovariates(
        age=rng.randint(*C.AGE_RANGE),
        weight=rng.uniform(*C.WEIGHT_RANGE),
        sex=rng.choice([0, 1]),
    )


def compute_effective_params(
    patient: PatientCovariates,
    cfg: SimulationConfig,
    rng: np.random.RandomState,
) -> EffectiveParams:
    """Derive patient-specific PK/PD parameters from covariates."""
    ke_eff = cfg.ke * (1 - C.AGE_KE_FACTOR * (patient.age - C.AGE_REFERENCE))
    ka_eff = cfg.ka * (1 - C.AGE_KA_FACTOR * (patient.age - C.AGE_REFERENCE))
    Vd_eff = cfg.Vd * (patient.weight / C.WEIGHT_REFERENCE)

    sex_mult = C.SEX_INFECTION_FACTOR if patient.sex == 1 else 1.0
    a_temp_inf_eff = cfg.a_temp_inf * sex_mult
    a_wbc_inf_eff = cfg.a_wbc_inf * sex_mult

    T_set = rng.normal(C.T_SETPOINT_MEAN, C.T_SETPOINT_SD)
    WBC_set = rng.normal(C.WBC_SETPOINT_MEAN, C.WBC_SETPOINT_SD)

    age_factor = 1 - C.AGE_VARIABILITY_FACTOR * (patient.age - C.AGE_REFERENCE)
    weight_factor = C.WEIGHT_REFERENCE / patient.weight

    lo, hi = C.VARIABILITY_RANGE
    k_inf_T_eff = cfg.k_inf_T * rng.uniform(lo, hi) * weight_factor
    k_home_T_eff = cfg.k_home_T * rng.uniform(lo, hi) * age_factor
    k_inf_W_eff = cfg.k_inf_W * rng.uniform(lo, hi) * weight_factor
    k_home_W_eff = cfg.k_home_W * rng.uniform(lo, hi) * age_factor

    return EffectiveParams(
        ke_eff=ke_eff,
        ka_eff=ka_eff,
        Vd_eff=Vd_eff,
        a_temp_inf_eff=a_temp_inf_eff,
        a_wbc_inf_eff=a_wbc_inf_eff,
        T_set=T_set,
        WBC_set=WBC_set,
        k_inf_T_eff=k_inf_T_eff,
        k_home_T_eff=k_home_T_eff,
        k_inf_W_eff=k_inf_W_eff,
        k_home_W_eff=k_home_W_eff,
    )


def compute_dose(T, WBC, conc, D_prev, cfg: SimulationConfig):
    """Feedback dosing controller: adjust dose based on vitals and concentration."""
    dose_temp = C.DOSE_VITAL_SCALE * max(0, T - cfg.T_norm[1])
    dose_wbc = C.DOSE_VITAL_SCALE * max(0, WBC - cfg.WBC_norm[1])
    dose_from_vitals = dose_temp + dose_wbc

    safety_factor = max(0, 1 - conc / cfg.C_max)
    D_t_raw = dose_from_vitals * safety_factor

    D_t = C.DOSE_SMOOTHING * D_prev + (1 - C.DOSE_SMOOTHING) * D_t_raw
    D_t = np.clip(D_t, cfg.D_min, cfg.D_max)
    return D_t


def simulate_patient(
    patient: PatientCovariates,
    params: EffectiveParams,
    cfg: SimulationConfig,
    rng: np.random.RandomState,
):
    """Run one patient through the PK/PD simulation.

    Returns (X, y) where X has shape (timesteps-1, 5) and y has shape (timesteps-1,).

    Changes:
    Now, this generates data for every hour, but a dose is only ever given every 12 hours
    """
    conc = C.INITIAL_C
    temp = rng.uniform(*C.INITIAL_T_RANGE)
    wbc = rng.uniform(*C.INITIAL_WBC_RANGE)
    D_prev = C.INITIAL_D_PREV

    X_patient = []
    y_patient = []

    # This is the concentration from dose d at time t
    curve = lambda d: lambda t: max(0, ((d * params.ka_eff)/(params.Vd_eff * (params.ka_eff - params.ke_eff))) * (math.exp(-params.ke_eff * t) - math.exp(-params.ka_eff * t)))
    # This is the total concentration of list ds at time t
    curve_funcs = lambda ds: lambda t: lambda ttd: list(map(lambda i: curve(ds[i])(t - i * ttd), list(range(len(ds)))))

    for i in range(cfg.timesteps - 1):
        D_t = compute_dose(temp, wbc, conc, D_prev, cfg)
        D_prev = D_t

        X_patient.append([conc, temp, wbc, patient.age, patient.weight])
        y_patient.append(D_t)

        ttd = 12
        # C_next is the trough concentration at the START of the next dosing interval
        # (i.e. at time (i+1)*ttd from t=0), which is what the patient presents
        # when the next dose decision is made.  This matches the semantics of
        # `x ! conc` in the Vehicle safeFarInput predicate, which is the plasma
        # concentration BEFORE the next dose is administered.
        C_next = sum(curve_funcs(y_patient)((i + 1) * ttd)(ttd))

        # Update PK/PD state
        # C_next = conc + cfg.dt * (-params.ke_eff * conc + D_t / params.Vd_eff)
        # C_next = max(0, C_next)

        T_next = temp + cfg.dt * (
            params.k_inf_T_eff
            - cfg.b_temp * conc
            - params.k_home_T_eff * (temp - params.T_set)
        )
        T_next = np.clip(T_next, *C.T_CLIP)

        WBC_next = wbc + cfg.dt * (
            params.k_inf_W_eff
            - cfg.c_wbc * conc
            - params.k_home_W_eff * (wbc - params.WBC_set)
        )
        WBC_next = np.clip(WBC_next, *C.WBC_CLIP)

        conc, temp, wbc = C_next, T_next, WBC_next

    return np.array(X_patient, dtype=np.float32), np.array(y_patient, dtype=np.float32)


def simulate_cohort(cfg: SimulationConfig = None, seed: int = None):
    """Simulate a cohort of patients.

    Returns (X, y) where X has shape (num_patients*(timesteps-1), 5) and
    y has shape (num_patients*(timesteps-1),).
    """
    if cfg is None:
        cfg = SimulationConfig()
    if seed is None:
        seed = cfg.seed

    rng = np.random.RandomState(seed)

    all_X = []
    all_y = []

    for _ in range(cfg.num_patients):
        patient = generate_patient_covariates(rng)
        params = compute_effective_params(patient, cfg, rng)
        X_p, y_p = simulate_patient(patient, params, cfg, rng)
        all_X.append(X_p)
        all_y.append(y_p)

    X = np.concatenate(all_X, axis=0)
    y = np.concatenate(all_y, axis=0)
    return X, y
