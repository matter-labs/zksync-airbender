import Airbender.Proofs.Keccak.SplitSlotReduction
import Airbender.Proofs.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace ParityPart1

private theorem round_4 (state : LaneState) :
    logicalLanes 4 (parityPhase 4 state) = iotaState (logicalLanes 4 state) 4 ∧
    (∀ column : Fin 5, parityPhase 4 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 4 state) 4))[column]) := by
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

private theorem round_5 (state : LaneState) :
    logicalLanes 5 (parityPhase 5 state) = iotaState (logicalLanes 5 state) 5 ∧
    (∀ column : Fin 5, parityPhase 5 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 5 state) 5))[column]) := by
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

private theorem round_6 (state : LaneState) :
    logicalLanes 6 (parityPhase 6 state) = iotaState (logicalLanes 6 state) 6 ∧
    (∀ column : Fin 5, parityPhase 6 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 6 state) 6))[column]) := by
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

private theorem round_7 (state : LaneState) :
    logicalLanes 7 (parityPhase 7 state) = iotaState (logicalLanes 7 state) 7 ∧
    (∀ column : Fin 5, parityPhase 7 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 7 state) 7))[column]) := by
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
    let round : Fin 24 := ⟨4 + part.val, by omega⟩
    logicalLanes round.val (parityPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) ∧
    (∀ column : Fin 5, parityPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column]) := by
  fin_cases part
  · exact round_4 state
  · exact round_5 state
  · exact round_6 state
  · exact round_7 state

end ParityPart1
end Airbender.Keccak.Split.Call.Proofs
