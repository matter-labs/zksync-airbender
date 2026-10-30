import Airbender.Proofs.Keccak.SplitParityPart0
import Airbender.Proofs.Keccak.SplitParityPart1
import Airbender.Proofs.Keccak.SplitParityPart2
import Airbender.Proofs.Keccak.SplitParityPart3
import Airbender.Proofs.Keccak.SplitParityPart4
import Airbender.Proofs.Keccak.SplitParityPart5

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- All 120 initial-round parity calls match the original delayed-iota reference. -/
theorem parity_phase_reference (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (parityPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) ∧
    (∀ column : Fin 5, parityPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column]) := by
  fin_cases round
  · exact ParityPart0.reference 0 state
  · exact ParityPart0.reference 1 state
  · exact ParityPart0.reference 2 state
  · exact ParityPart0.reference 3 state
  · exact ParityPart1.reference 0 state
  · exact ParityPart1.reference 1 state
  · exact ParityPart1.reference 2 state
  · exact ParityPart1.reference 3 state
  · exact ParityPart2.reference 0 state
  · exact ParityPart2.reference 1 state
  · exact ParityPart2.reference 2 state
  · exact ParityPart2.reference 3 state
  · exact ParityPart3.reference 0 state
  · exact ParityPart3.reference 1 state
  · exact ParityPart3.reference 2 state
  · exact ParityPart3.reference 3 state
  · exact ParityPart4.reference 0 state
  · exact ParityPart4.reference 1 state
  · exact ParityPart4.reference 2 state
  · exact ParityPart4.reference 3 state
  · exact ParityPart5.reference 0 state
  · exact ParityPart5.reference 1 state
  · exact ParityPart5.reference 2 state
  · exact ParityPart5.reference 3 state

end Airbender.Keccak.Split.Call.Proofs
