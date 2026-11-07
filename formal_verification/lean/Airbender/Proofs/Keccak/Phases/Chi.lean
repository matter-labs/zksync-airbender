import Airbender.Proofs.Keccak.Phases.ChiPart0
import Airbender.Proofs.Keccak.Phases.ChiPart1
import Airbender.Proofs.Keccak.Phases.ChiPart2
import Airbender.Proofs.Keccak.Phases.ChiPart3
import Airbender.Proofs.Keccak.Phases.ChiPart4
import Airbender.Proofs.Keccak.Phases.ChiPart5

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option Elab.async false

theorem chi_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (chiPhase round state) = chi (logicalLanes (round.val + 1) state) := by
  fin_cases round
  · exact ChiPart0.lanes 0 state
  · exact ChiPart0.lanes 1 state
  · exact ChiPart0.lanes 2 state
  · exact ChiPart0.lanes 3 state
  · exact ChiPart1.lanes 0 state
  · exact ChiPart1.lanes 1 state
  · exact ChiPart1.lanes 2 state
  · exact ChiPart1.lanes 3 state
  · exact ChiPart2.lanes 0 state
  · exact ChiPart2.lanes 1 state
  · exact ChiPart2.lanes 2 state
  · exact ChiPart2.lanes 3 state
  · exact ChiPart3.lanes 0 state
  · exact ChiPart3.lanes 1 state
  · exact ChiPart3.lanes 2 state
  · exact ChiPart3.lanes 3 state
  · exact ChiPart4.lanes 0 state
  · exact ChiPart4.lanes 1 state
  · exact ChiPart4.lanes 2 state
  · exact ChiPart4.lanes 3 state
  · exact ChiPart5.lanes 0 state
  · exact ChiPart5.lanes 1 state
  · exact ChiPart5.lanes 2 state
  · exact ChiPart5.lanes 3 state

end Airbender.Keccak.Proofs
