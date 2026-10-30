import Airbender.Proofs.Keccak.SplitSlotReduction
import Airbender.Proofs.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace ParityPart3

private theorem round_12 (state : LaneState) :
    logicalLanes 12 (parityPhase 12 state) = iotaState (logicalLanes 12 state) 12 ∧
    (∀ column : Fin 5, parityPhase 12 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 12 state) 12))[column]) := by
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

private theorem round_13 (state : LaneState) :
    logicalLanes 13 (parityPhase 13 state) = iotaState (logicalLanes 13 state) 13 ∧
    (∀ column : Fin 5, parityPhase 13 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 13 state) 13))[column]) := by
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

private theorem round_14 (state : LaneState) :
    logicalLanes 14 (parityPhase 14 state) = iotaState (logicalLanes 14 state) 14 ∧
    (∀ column : Fin 5, parityPhase 14 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 14 state) 14))[column]) := by
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

private theorem round_15 (state : LaneState) :
    logicalLanes 15 (parityPhase 15 state) = iotaState (logicalLanes 15 state) 15 ∧
    (∀ column : Fin 5, parityPhase 15 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 15 state) 15))[column]) := by
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
    let round : Fin 24 := ⟨12 + part.val, by omega⟩
    logicalLanes round.val (parityPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) ∧
    (∀ column : Fin 5, parityPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column]) := by
  fin_cases part
  · exact round_12 state
  · exact round_13 state
  · exact round_14 state
  · exact round_15 state

end ParityPart3
end Airbender.Keccak.Split.Call.Proofs
