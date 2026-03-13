type UnnormalisedInputVector = Tensor Real [5]
type InputVector = Tensor Real [5]

conc = 0
temp = 1
wbc = 2
age = 3
weight = 4

type OutputVector= Tensor Real [1]

meanScalingValues : UnnormalisedInputVector
meanScalingValues = [13.43430467, 37.73065665, 11.87602918, 50.80319149, 76.4415882]

standardDeviationValues : UnnormalisedInputVector
standardDeviationValues =  [7.31223371, 0.62039077, 2.54280181, 23.16670829, 14.39579016]

normalise : UnnormalisedInputVector -> InputVector
normalise x = foreach i .
  (x ! i - meanScalingValues ! i) / (standardDeviationValues ! i)

@network
pk : InputVector -> OutputVector

normpk : UnnormalisedInputVector -> OutputVector
normpk x = pk (normalise x)

@parameter
Ka : Real

@property
Ka_pos : Bool
Ka_pos = 0 < Ka

@parameter
Ke : Real

@property
Ke_pos : Bool
Ke_pos = 0 < Ke

@property
Ke_n_Ka : Bool
Ke_n_Ka = Ka != Ke

@parameter
Vd : Real

@property
Vd_pos : Bool
Vd_pos = 0 < Vd

@parameter
C_safe : Real

@property
C_safe_pos : Bool
C_safe_pos = 0 < C_safe

@parameter
ttd : Real

@property
ttd_pos : Bool
ttd_pos = 0 < ttd

@parameter
Ka_over : Real
-- e^-ka * (ln(ka/ke)/(ka-ke))

@parameter
Ka_under : Real

@parameter
Ke_over : Real
-- e^-ke * (ln(ka/ke)/(ka-ke))

@parameter
Ke_under : Real

@parameter
eps : Real

safeFarInput : InputVector -> Bool
safeFarInput x = 
    0 <= x ! conc <= C_safe * 0.99 and
    36.5 <= x ! temp <= 40 and
    7.5 <= x ! wbc <= 20 and
    18 <= x ! age <= 89 and
    50 <= x ! weight <= 100

safeFarOutput : InputVector -> Bool
safeFarOutput x = let y = ((((normpk x) ! 0) * Ka) / (Vd * (Ka - Ke))) in
           if Ka < Ke
           then (x ! conc) + y * (Ke_under - Ka_over) < C_safe
           else (x ! conc) + y * (Ke_over - Ka_under) < C_safe
           -- C + C(D, max_root) < C_safe

@property
safeFar : Bool
safeFar = forall x . safeFarInput x => safeFarOutput x

safeNearInput : InputVector -> Bool
safeNearInput x = 
    C_safe * 0.99 <= x ! conc <= C_safe and
    36.5 <= x ! temp <= 40 and
    7.5 <= x ! wbc <= 20 and
    18 <= x ! age <= 89 and
    50 <= x ! weight <= 100

safeNearOutput : InputVector -> Bool
safeNearOutput x = ((normpk x) ! 0) < eps

@property
safeNear : Bool
safeNear = forall x . safeNearInput x => safeNearOutput x

safeInput : InputVector -> Bool
safeInput x = 
    0 <= x ! conc <= C_safe and
    36.5 <= x ! temp <= 40 and
    7.5 <= x ! wbc <= 20 and
    18 <= x ! age <= 89 and
    50 <= x ! weight <= 100

nonNegOutput : InputVector -> Bool
nonNegOutput x =  0 < (normpk x) ! 0

@property
nonNeg : Bool
nonNeg = forall x . safeInput x => nonNegOutput x
