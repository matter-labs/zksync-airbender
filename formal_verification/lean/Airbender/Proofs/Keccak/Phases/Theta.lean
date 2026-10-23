import Airbender.Proofs.Keccak.Phases.ThetaPart0
import Airbender.Proofs.Keccak.Phases.ThetaPart1
import Airbender.Proofs.Keccak.Phases.ThetaPart2
import Airbender.Proofs.Keccak.Phases.ThetaPart3
import Airbender.Proofs.Keccak.Phases.ThetaPart4
import Airbender.Proofs.Keccak.Phases.ThetaPart5

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option Elab.async false

theorem theta_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (thetaPhase round state) =
      thetaXor (logicalLanes round.val state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  fin_cases round
  · exact ThetaPart0.lanes 0 state
  · exact ThetaPart0.lanes 1 state
  · exact ThetaPart0.lanes 2 state
  · exact ThetaPart0.lanes 3 state
  · exact ThetaPart1.lanes 0 state
  · exact ThetaPart1.lanes 1 state
  · exact ThetaPart1.lanes 2 state
  · exact ThetaPart1.lanes 3 state
  · exact ThetaPart2.lanes 0 state
  · exact ThetaPart2.lanes 1 state
  · exact ThetaPart2.lanes 2 state
  · exact ThetaPart2.lanes 3 state
  · exact ThetaPart3.lanes 0 state
  · exact ThetaPart3.lanes 1 state
  · exact ThetaPart3.lanes 2 state
  · exact ThetaPart3.lanes 3 state
  · exact ThetaPart4.lanes 0 state
  · exact ThetaPart4.lanes 1 state
  · exact ThetaPart4.lanes 2 state
  · exact ThetaPart4.lanes 3 state
  · exact ThetaPart5.lanes 0 state
  · exact ThetaPart5.lanes 1 state
  · exact ThetaPart5.lanes 2 state
  · exact ThetaPart5.lanes 3 state

end Airbender.Keccak.Proofs
