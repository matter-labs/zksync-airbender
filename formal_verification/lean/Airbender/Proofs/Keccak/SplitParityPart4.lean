import Airbender.Proofs.Keccak.SplitSlotReduction
import Airbender.Proofs.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace ParityPart4

private theorem round_16 (state : LaneState) :
    logicalLanes 16 (parityPhase 16 state) = iotaState (logicalLanes 16 state) 16 ∧
    (∀ column : Fin 5, parityPhase 16 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 16 state) 16))[column]) := by
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

private theorem round_17 (state : LaneState) :
    logicalLanes 17 (parityPhase 17 state) = iotaState (logicalLanes 17 state) 17 ∧
    (∀ column : Fin 5, parityPhase 17 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 17 state) 17))[column]) := by
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

private theorem round_18 (state : LaneState) :
    logicalLanes 18 (parityPhase 18 state) = iotaState (logicalLanes 18 state) 18 ∧
    (∀ column : Fin 5, parityPhase 18 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 18 state) 18))[column]) := by
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

private theorem round_19 (state : LaneState) :
    logicalLanes 19 (parityPhase 19 state) = iotaState (logicalLanes 19 state) 19 ∧
    (∀ column : Fin 5, parityPhase 19 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 19 state) 19))[column]) := by
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
    let round : Fin 24 := ⟨16 + part.val, by omega⟩
    logicalLanes round.val (parityPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) ∧
    (∀ column : Fin 5, parityPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column]) := by
  fin_cases part
  · exact round_16 state
  · exact round_17 state
  · exact round_18 state
  · exact round_19 state

end ParityPart4
end Airbender.Keccak.Split.Call.Proofs
