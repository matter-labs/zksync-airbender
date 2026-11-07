import Airbender.Proofs.Keccak.SplitThetaRhoPart0
import Airbender.Proofs.Keccak.SplitThetaRhoPart1
import Airbender.Proofs.Keccak.SplitThetaRhoPart2
import Airbender.Proofs.Keccak.SplitThetaRhoPart3
import Airbender.Proofs.Keccak.SplitThetaRhoPart4
import Airbender.Proofs.Keccak.SplitThetaRhoPart5

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- All twenty-four split phases match the original Keccak reference. -/
theorem theta_rho_phase_reference (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (thetaRhoPhase round state) =
      rhoPi (thetaXor (logicalLanes round.val state)
        (thetaD (Vector.ofFn fun column : Fin 5 => state ⟨25 + column.val, by omega⟩))) := by
  fin_cases round
  · exact ThetaRhoPart0.reference 0 state
  · exact ThetaRhoPart0.reference 1 state
  · exact ThetaRhoPart0.reference 2 state
  · exact ThetaRhoPart0.reference 3 state
  · exact ThetaRhoPart1.reference 0 state
  · exact ThetaRhoPart1.reference 1 state
  · exact ThetaRhoPart1.reference 2 state
  · exact ThetaRhoPart1.reference 3 state
  · exact ThetaRhoPart2.reference 0 state
  · exact ThetaRhoPart2.reference 1 state
  · exact ThetaRhoPart2.reference 2 state
  · exact ThetaRhoPart2.reference 3 state
  · exact ThetaRhoPart3.reference 0 state
  · exact ThetaRhoPart3.reference 1 state
  · exact ThetaRhoPart3.reference 2 state
  · exact ThetaRhoPart3.reference 3 state
  · exact ThetaRhoPart4.reference 0 state
  · exact ThetaRhoPart4.reference 1 state
  · exact ThetaRhoPart4.reference 2 state
  · exact ThetaRhoPart4.reference 3 state
  · exact ThetaRhoPart5.reference 0 state
  · exact ThetaRhoPart5.reference 1 state
  · exact ThetaRhoPart5.reference 2 state
  · exact ThetaRhoPart5.reference 3 state

end Airbender.Keccak.Split.Call.Proofs
