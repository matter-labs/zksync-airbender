import Airbender.Proofs.Keccak.SplitChiPart0
import Airbender.Proofs.Keccak.SplitChiPart1
import Airbender.Proofs.Keccak.SplitChiPart2
import Airbender.Proofs.Keccak.SplitChiPart3
import Airbender.Proofs.Keccak.SplitChiPart4
import Airbender.Proofs.Keccak.SplitChiPart5

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- All twenty-four split phases match the original Keccak reference. -/
theorem chi_phase_reference (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (chiPhase round state) =
      chi (logicalLanes (round.val + 1) state) := by
  fin_cases round
  · exact ChiPart0.reference 0 state
  · exact ChiPart0.reference 1 state
  · exact ChiPart0.reference 2 state
  · exact ChiPart0.reference 3 state
  · exact ChiPart1.reference 0 state
  · exact ChiPart1.reference 1 state
  · exact ChiPart1.reference 2 state
  · exact ChiPart1.reference 3 state
  · exact ChiPart2.reference 0 state
  · exact ChiPart2.reference 1 state
  · exact ChiPart2.reference 2 state
  · exact ChiPart2.reference 3 state
  · exact ChiPart3.reference 0 state
  · exact ChiPart3.reference 1 state
  · exact ChiPart3.reference 2 state
  · exact ChiPart3.reference 3 state
  · exact ChiPart4.reference 0 state
  · exact ChiPart4.reference 1 state
  · exact ChiPart4.reference 2 state
  · exact ChiPart4.reference 3 state
  · exact ChiPart5.reference 0 state
  · exact ChiPart5.reference 1 state
  · exact ChiPart5.reference 2 state
  · exact ChiPart5.reference 3 state

end Airbender.Keccak.Split.Call.Proofs
