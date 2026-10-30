import Airbender.Proofs.Keccak.SplitSlotReduction
import Airbender.Proofs.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace ParityPart5

private theorem round_20 (state : LaneState) :
    logicalLanes 20 (parityPhase 20 state) = iotaState (logicalLanes 20 state) 20 ∧
    (∀ column : Fin 5, parityPhase 20 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 20 state) 20))[column]) := by
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

private theorem round_21 (state : LaneState) :
    logicalLanes 21 (parityPhase 21 state) = iotaState (logicalLanes 21 state) 21 ∧
    (∀ column : Fin 5, parityPhase 21 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 21 state) 21))[column]) := by
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

private theorem round_22 (state : LaneState) :
    logicalLanes 22 (parityPhase 22 state) = iotaState (logicalLanes 22 state) 22 ∧
    (∀ column : Fin 5, parityPhase 22 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 22 state) 22))[column]) := by
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

private theorem round_23 (state : LaneState) :
    logicalLanes 23 (parityPhase 23 state) = iotaState (logicalLanes 23 state) 23 ∧
    (∀ column : Fin 5, parityPhase 23 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 23 state) 23))[column]) := by
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
    let round : Fin 24 := ⟨20 + part.val, by omega⟩
    logicalLanes round.val (parityPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) ∧
    (∀ column : Fin 5, parityPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column]) := by
  fin_cases part
  · exact round_20 state
  · exact round_21 state
  · exact round_22 state
  · exact round_23 state

end ParityPart5
end Airbender.Keccak.Split.Call.Proofs
