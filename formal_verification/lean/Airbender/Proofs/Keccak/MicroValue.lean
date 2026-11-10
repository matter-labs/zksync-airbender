import Airbender.Proofs.Keccak.MicroValueDefinitions
import Airbender.Proofs.Keccak.MicroOperations

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

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
