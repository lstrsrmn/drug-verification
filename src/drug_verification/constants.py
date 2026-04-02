"""Named constants for the PK/PD simulation and training pipeline."""

# --- Simulation parameters ---
TIMESTEPS = 48
DT = 12
NUM_PATIENTS = 50

# --- Baseline PK/PD parameters ---
KE = 0.1          # baseline elimination rate (per hour)
KA = 4.5          # baseline absorption rate (per hour)
TTD = 12          # time between doses (hours)
VD = 30           # baseline volume of distribution (L)
B_TEMP = 0.005    # drug effect on temperature
C_WBC = 0.02      # drug effect on WBC
A_TEMP_INF = 0.05 # infection effect on temperature (no drug)
A_WBC_INF = 0.1   # infection effect on WBC (no drug)
K_INF_T = 0.08    # infection-driven temperature rise rate
K_HOME_T = 0.12   # homeostatic temperature correction rate
K_INF_W = 0.12    # infection-driven WBC rise rate
K_HOME_W = 0.04   # homeostatic WBC correction rate

# --- Normal ranges / targets ---
T_NORM = (36.0, 38.0)   # normal temperature range (°C)
WBC_NORM = (4.0, 12.0)  # normal WBC range (thousand/µL)
C_MAX = 30               # drug toxic maximum concentration (µg/mL)

# --- Dose bounds ---
D_MIN = 0      # minimum dose (mg)
D_MAX = 1500   # maximum dose (mg)

# --- Patient covariate ranges ---
AGE_RANGE = (18, 90)
WEIGHT_RANGE = (50.0, 100.0)

# --- Covariate adjustment factors ---
AGE_KE_FACTOR = 0.004       # ke reduction per year above 50
AGE_KA_FACTOR = 0.004       # ka reduction per year above 50
AGE_REFERENCE = 50           # reference age for covariate adjustments
WEIGHT_REFERENCE = 70.0      # reference weight (kg) for Vd scaling
SEX_INFECTION_FACTOR = 1.1   # female infection effect multiplier
SEX_PK_FACTOR = 1.05         # female PK factor (unused in current sim)

# --- Homeostasis setpoint distributions ---
T_SETPOINT_MEAN = 37.0      # °C
T_SETPOINT_SD = 0.2
WBC_SETPOINT_MEAN = 8.0     # thousand/µL
WBC_SETPOINT_SD = 1.0

# --- Variability multiplier factors ---
AGE_VARIABILITY_FACTOR = 0.003   # per-year effect on variability
VARIABILITY_RANGE = (0.9, 1.1)   # uniform range for random multipliers

# --- Initial conditions ---
INITIAL_C = 0.0
INITIAL_T_RANGE = (38.5, 40.0)   # initial sick temperature
INITIAL_WBC_RANGE = (12.0, 20.0) # initial sick WBC
INITIAL_D_PREV = 500             # initial previous dose (mg)

# --- Dosing controller ---
DOSE_VITAL_SCALE = 50       # dose scaling factor for vital sign deviation
DOSE_SMOOTHING = 0.7        # weight on previous dose (inertia)

# --- Physiological clipping bounds ---
T_CLIP = (35.0, 42.0)       # temperature clipping range (°C)
WBC_CLIP = (1.0, 30.0)      # WBC clipping range (thousand/µL)

# --- Training defaults ---
DEFAULT_HIDDEN_SIZES = (128, 64)
DEFAULT_EPOCHS = 100
DEFAULT_BATCH_SIZE = 32
DEFAULT_TEST_SIZE = 0.2
DEFAULT_SEED = 42

# --- Constraint-training defaults (GradNorm) ---
DEFAULT_GRADNORM_ALPHA = 0.5
DEFAULT_GRADNORM_WEIGHT_LR = 1e-3
DEFAULT_GRADNORM_MIN_WEIGHT = 0.05
DEFAULT_INITIAL_CONSTRAINT_WEIGHT = 1.0
DEFAULT_INITIAL_CONSTRAINT2_WEIGHT = 1.0
DEFAULT_OPTIMIZER_LR = 1e-3

# --- Optuna tuning defaults ---
DEFAULT_OPTUNA_N_TRIALS = 25
DEFAULT_OPTUNA_TIMEOUT_SECONDS = 1800
DEFAULT_OPTUNA_STORAGE = "sqlite:///optuna_vehicle.db"
DEFAULT_OPTUNA_STUDY_NAME = "vehicle_loss_hpo"
DEFAULT_OPTUNA_PRUNER = "median"
DEFAULT_TUNE_CONSTRAINT_OBJECTIVE_WEIGHT = 0.1
DEFAULT_TUNE_CONSTRAINT2_OBJECTIVE_WEIGHT = 0.1

TUNE_N_LAYERS_RANGE = (1, 3)
TUNE_UNITS_RANGE = (32, 256)
TUNE_BATCH_SIZE_CHOICES = (16, 32, 64)
TUNE_LEARNING_RATE_RANGE = (1e-4, 3e-3)
TUNE_GRADNORM_ALPHA_RANGE = (0.1, 1.5)
TUNE_GRADNORM_WEIGHT_LR_RANGE = (1e-4, 1e-2)
TUNE_INITIAL_CONSTRAINT_WEIGHT_RANGE = (0.25, 1.75)

# --- Verification/spec defaults ---
DEFAULT_SPEC_PARAMS = {
    "Ka": 4.5,
    "Ke": 3.5,
    "Vd": 10,
    "C_safe": 30,
    "ttd": 2,
    "Ka_over": 0.3228,
    "Ka_under": 0.3227,
    "Ke_over": 0.415,
    "Ke_under": 0.4149,
    "eps": 0.001,
}

