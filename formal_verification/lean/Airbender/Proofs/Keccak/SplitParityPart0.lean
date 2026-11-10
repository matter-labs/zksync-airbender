import Airbender.Proofs.Keccak.SplitSlotReduction
import Airbender.Proofs.Keccak.LayoutReduction
import Airbender.Proofs.Keccak.SplitParityPhase
import Airbender.Proofs.Keccak.SplitParityRounds

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace ParityPart0

private theorem round_2 (state : LaneState) :
    logicalLanes 2 (parityPhase 2 state) = iotaState (logicalLanes 2 state) 2 ∧
    (∀ column : Fin 5, parityPhase 2 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 2 state) 2))[column]) := by
  constructor
  · apply Vector.ext
    intro lane bound
    interval_cases lane
    all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
    all_goals rfl'
  · intro column
    fin_cases column
    all_goals simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
    all_goals rfl'

private theorem round_3 (state : LaneState) :
    logicalLanes 3 (parityPhase 3 state) = iotaState (logicalLanes 3 state) 3 ∧
    (∀ column : Fin 5, parityPhase 3 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 3 state) 3))[column]) := by
  constructor
  · apply Vector.ext
    intro lane bound
    interval_cases lane
    all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
    all_goals rfl'
  · intro column
    fin_cases column
    all_goals simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
    all_goals rfl'

/-- Four exact parity phases use the original delayed-iota reference. -/
theorem reference (part : Fin 4) (state : LaneState) :
    let round : Fin 24 := ⟨0 + part.val, by omega⟩
    logicalLanes round.val (parityPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) ∧
    (∀ column : Fin 5, parityPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column]) := by
  fin_cases part
  · exact parity_phase_round_zero state
  · exact parity_phase_round_one state
  · exact round_2 state
  · exact round_3 state

end ParityPart0
end Airbender.Keccak.Split.Call.Proofs
