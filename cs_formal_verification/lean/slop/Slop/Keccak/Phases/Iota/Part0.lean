import Slop.Keccak.PhaseDefinitions
import Slop.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000
set_option cbv.maxSteps 2000000
attribute [local cbv_opaque] rotLeft64 not64 Nat.xor Nat.land roundConstants

local macro "solve_iota_lanes" : tactic => `(tactic| (
  apply Vector.ext
  intro i bound
  interval_cases i <;>
    simp only [logicalLanes, Vector.getElem_ofFn, iotaPhase, Fin.foldl_succ_last,
      Fin.foldl_zero, physical_cached, micro_normalized] <;> cbv))
local macro "solve_iota_parities" column:term : tactic => `(tactic| (
  fin_cases $column:term <;>
    simp only [logicalLanes, Vector.getElem_ofFn, iotaPhase, Fin.foldl_succ_last, Fin.foldl_zero,
      physical_cached, micro_normalized] <;> cbv))

theorem iota_lanes_0 (state : LaneState) :
    logicalLanes 0 (iotaPhase 0 state) =
      iotaState (logicalLanes 0 state) (Fin.ofNat 25 0) := by solve_iota_lanes
theorem iota_parities_0 (state : LaneState) (column : Fin 5) :
    iotaPhase 0 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 0 state) (Fin.ofNat 25 0)))[column] := by solve_iota_parities column
theorem iota_lanes_1 (state : LaneState) :
    logicalLanes 1 (iotaPhase 1 state) =
      iotaState (logicalLanes 1 state) (Fin.ofNat 25 1) := by solve_iota_lanes
theorem iota_parities_1 (state : LaneState) (column : Fin 5) :
    iotaPhase 1 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 1 state) (Fin.ofNat 25 1)))[column] := by solve_iota_parities column
theorem iota_lanes_2 (state : LaneState) :
    logicalLanes 2 (iotaPhase 2 state) =
      iotaState (logicalLanes 2 state) (Fin.ofNat 25 2) := by solve_iota_lanes
theorem iota_parities_2 (state : LaneState) (column : Fin 5) :
    iotaPhase 2 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 2 state) (Fin.ofNat 25 2)))[column] := by solve_iota_parities column
theorem iota_lanes_3 (state : LaneState) :
    logicalLanes 3 (iotaPhase 3 state) =
      iotaState (logicalLanes 3 state) (Fin.ofNat 25 3) := by solve_iota_lanes
theorem iota_parities_3 (state : LaneState) (column : Fin 5) :
    iotaPhase 3 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 3 state) (Fin.ofNat 25 3)))[column] := by solve_iota_parities column
theorem iota_lanes_4 (state : LaneState) :
    logicalLanes 4 (iotaPhase 4 state) =
      iotaState (logicalLanes 4 state) (Fin.ofNat 25 4) := by solve_iota_lanes
theorem iota_parities_4 (state : LaneState) (column : Fin 5) :
    iotaPhase 4 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 4 state) (Fin.ofNat 25 4)))[column] := by solve_iota_parities column
theorem iota_lanes_5 (state : LaneState) :
    logicalLanes 5 (iotaPhase 5 state) =
      iotaState (logicalLanes 5 state) (Fin.ofNat 25 5) := by solve_iota_lanes
theorem iota_parities_5 (state : LaneState) (column : Fin 5) :
    iotaPhase 5 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 5 state) (Fin.ofNat 25 5)))[column] := by solve_iota_parities column

end Airbender.Keccak.Proofs
