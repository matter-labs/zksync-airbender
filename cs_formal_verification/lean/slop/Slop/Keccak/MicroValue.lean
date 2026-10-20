import Slop.Keccak.MicroOperations

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def iotaValue (control : ControlState) (read : Fin 6 → Nat) (lane : Fin 6) : Nat :=
  if h : control.iteration.val = 0 ∧ lane.val = 0 ∧ 0 < control.round.val then
    read lane ^^^ Specs.Keccak256.roundConstants[Fin.ofNat 24 (control.round.val - 1)].toFin
  else read lane

def microValue (control : ControlState) (read : Fin 6 → Nat) (lane : Fin 6) : Nat :=
  if control.mode = 0 then
    if lane.val < 5 then iotaValue control read lane else
      iotaValue control read 0 ^^^ read 1 ^^^ read 2 ^^^ read 3 ^^^ read 4
  else if control.mode = 1 then
    if lane = 0 then read 0 ^^^ rotLeft64 (read 2) 1
    else if lane = 2 then read 2 ^^^ rotLeft64 (read 4) 1
    else if lane = 5 then rotLeft64 (read 0) 1 else read lane
  else if control.mode = 2 then
    if lane = 1 then read 1 ^^^ rotLeft64 (read 3) 1
    else if lane = 3 then read 3 ^^^ read 5
    else if lane = 4 then read 4 ^^^ rotLeft64 (read 1) 1 else read lane
  else if control.mode = 3 then
    if lane.val < 5 then read lane ^^^ read 5 else read 5
  else if control.mode = 4 then
    if h : lane.val < 5 then rotLeft64 (read lane) rhoRotations[control.iteration][lane.val] else read 5
  else if control.mode = 5 then
    if lane = 0 then read 0 ^^^ ((not64 (read 1)) &&& read 2)
    else if lane = 1 then read 1 ^^^ ((not64 (read 2)) &&& read 3)
    else if lane = 4 then (not64 (read 0)) &&& read 1
    else if lane = 5 then read 0 else read lane
  else
    if lane = 0 then read 0 ^^^ read 3
    else if lane = 1 then read 1 ^^^ ((not64 (read 2)) &&& read 0)
    else if lane = 2 then read 2 ^^^ ((not64 (read 0)) &&& read 4) else read lane

theorem micro_value_eq (control : ControlState) (bound : control.round.val < 25)
    (read : Fin 6 → Nat) (lane : Fin 6) :
    (microWrites control (Vector.ofFn read))[lane] = microValue control read lane := by
  have modRound : control.round.val % 25 = control.round.val := Nat.mod_eq_of_lt bound
  have rcBound : control.round.val - 1 < 24 := by omega
  have modRC : (control.round.val - 1) % 24 = control.round.val - 1 := Nat.mod_eq_of_lt rcBound
  generalize mode : control.mode = selected
  fin_cases selected
  · by_cases positive : 0 < control.round.val
    · generalize iteration : control.iteration = column
      fin_cases column
      all_goals fin_cases lane
      all_goals simp [microWrites, microValue, iotaValue, columnState, iotaState,
        Specs.Keccak256.iota, Specs.Keccak256.thetaC, mode, iteration, positive, modRound, modRC]
    · generalize iteration : control.iteration = column
      fin_cases column
      all_goals fin_cases lane
      all_goals simp [microWrites, microValue, iotaValue, columnState, iotaState,
        Specs.Keccak256.thetaC, mode, iteration, positive, modRound]
  all_goals fin_cases lane
  all_goals simp [microWrites, microValue, mode]

end Airbender.Keccak.Proofs
