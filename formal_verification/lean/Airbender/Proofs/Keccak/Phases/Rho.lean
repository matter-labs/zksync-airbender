import Airbender.Proofs.Keccak.Phases.RhoPart0
import Airbender.Proofs.Keccak.Phases.RhoPart1
import Airbender.Proofs.Keccak.Phases.RhoPart2
import Airbender.Proofs.Keccak.Phases.RhoPart3
import Airbender.Proofs.Keccak.Phases.RhoPart4
import Airbender.Proofs.Keccak.Phases.RhoPart5

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option Elab.async false

theorem rho_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (rhoPhase round state) = rhoPi (logicalLanes round.val state) := by
  fin_cases round
  · exact RhoPart0.lanes 0 state
  · exact RhoPart0.lanes 1 state
  · exact RhoPart0.lanes 2 state
  · exact RhoPart0.lanes 3 state
  · exact RhoPart1.lanes 0 state
  · exact RhoPart1.lanes 1 state
  · exact RhoPart1.lanes 2 state
  · exact RhoPart1.lanes 3 state
  · exact RhoPart2.lanes 0 state
  · exact RhoPart2.lanes 1 state
  · exact RhoPart2.lanes 2 state
  · exact RhoPart2.lanes 3 state
  · exact RhoPart3.lanes 0 state
  · exact RhoPart3.lanes 1 state
  · exact RhoPart3.lanes 2 state
  · exact RhoPart3.lanes 3 state
  · exact RhoPart4.lanes 0 state
  · exact RhoPart4.lanes 1 state
  · exact RhoPart4.lanes 2 state
  · exact RhoPart4.lanes 3 state
  · exact RhoPart5.lanes 0 state
  · exact RhoPart5.lanes 1 state
  · exact RhoPart5.lanes 2 state
  · exact RhoPart5.lanes 3 state

end Airbender.Keccak.Proofs
