type UnnormalisedInputVector = Tensor Real [6]
type InputVector = Tensor Real [6]

conc = 0
temp = 1
wbc = 2
age = 3
weight = 4
sex = 5

type OutputVector= Tensor Real [1]

meanScalingValues : UnnormalisedInputVector
meanScalingValues = [13.41985028, 37.73609288, 11.88956131, 50.64, 76.37743713,  0.6]

standardDeviationValues : UnnormalisedInputVector
standardDeviationValues =  [7.32717627, 0.625989, 2.54834216, 23.22477987, 14.33796805, 0.48989795]

normalise : UnnormalisedInputVector -> InputVector
normalise x = foreach i .
  (x ! i - meanScalingValues ! i) / (standardDeviationValues ! i)

@network
pk : InputVector -> OutputVector

normpk : UnnormalisedInputVector -> OutputVector
normpk x = pk (x)

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

@parameter
Ka_under : Real

@parameter
Ke_over : Real

@parameter
Ke_under : Real

@parameter
eps : Real

safeFarInput : InputVector -> Bool
safeFarInput x = 
    0 <= x ! conc <= C_safe - 1 and
    36.5 <= x ! temp <= 40 and
    7.5 <= x ! wbc <= 20 and
    18 <= x ! age <= 89 and
    50 <= x ! weight <= 100 and
    0 <= x ! sex <= 1

safeFarOutput : InputVector -> Bool
safeFarOutput x = let y =  ((((normpk x) ! 0) * Ka) / (Vd * (Ka - Ke))) in
           if Ka < Ke
           then (x ! conc) + y * (Ke_under - Ka_over) < C_safe
           else (x ! conc) + y * (Ke_over - Ka_under) < C_safe

@property
safeFar : Bool
safeFar = forall x . safeFarInput x => safeFarOutput x

safeNearInput : InputVector -> Bool
safeNearInput x = 
    C_safe - 1 <= x ! conc <= C_safe and
    36.5 <= x ! temp <= 40 and
    7.5 <= x ! wbc <= 20 and
    18 <= x ! age <= 89 and
    50 <= x ! weight <= 100 and
    0 <= x ! sex <= 1

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
    50 <= x ! weight <= 100 and
    0 <= x ! sex <= 1

nonNegOutput : InputVector -> Bool
nonNegOutput x =  0 < (normpk x) ! 0

@property
nonNeg : Bool
nonNeg = forall x . safeInput x => nonNegOutput x
