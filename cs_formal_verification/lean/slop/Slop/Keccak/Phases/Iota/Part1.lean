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

theorem iota_lanes_6 (state : LaneState) :
    logicalLanes 6 (iotaPhase 6 state) =
      iotaState (logicalLanes 6 state) (Fin.ofNat 25 6) := by solve_iota_lanes
theorem iota_parities_6 (state : LaneState) (column : Fin 5) :
    iotaPhase 6 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 6 state) (Fin.ofNat 25 6)))[column] := by solve_iota_parities column
theorem iota_lanes_7 (state : LaneState) :
    logicalLanes 7 (iotaPhase 7 state) =
      iotaState (logicalLanes 7 state) (Fin.ofNat 25 7) := by solve_iota_lanes
theorem iota_parities_7 (state : LaneState) (column : Fin 5) :
    iotaPhase 7 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 7 state) (Fin.ofNat 25 7)))[column] := by solve_iota_parities column
theorem iota_lanes_8 (state : LaneState) :
    logicalLanes 8 (iotaPhase 8 state) =
      iotaState (logicalLanes 8 state) (Fin.ofNat 25 8) := by solve_iota_lanes
theorem iota_parities_8 (state : LaneState) (column : Fin 5) :
    iotaPhase 8 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 8 state) (Fin.ofNat 25 8)))[column] := by solve_iota_parities column
theorem iota_lanes_9 (state : LaneState) :
    logicalLanes 9 (iotaPhase 9 state) =
      iotaState (logicalLanes 9 state) (Fin.ofNat 25 9) := by solve_iota_lanes
theorem iota_parities_9 (state : LaneState) (column : Fin 5) :
    iotaPhase 9 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 9 state) (Fin.ofNat 25 9)))[column] := by solve_iota_parities column
theorem iota_lanes_10 (state : LaneState) :
    logicalLanes 10 (iotaPhase 10 state) =
      iotaState (logicalLanes 10 state) (Fin.ofNat 25 10) := by solve_iota_lanes
theorem iota_parities_10 (state : LaneState) (column : Fin 5) :
    iotaPhase 10 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 10 state) (Fin.ofNat 25 10)))[column] := by solve_iota_parities column
theorem iota_lanes_11 (state : LaneState) :
    logicalLanes 11 (iotaPhase 11 state) =
      iotaState (logicalLanes 11 state) (Fin.ofNat 25 11) := by solve_iota_lanes
theorem iota_parities_11 (state : LaneState) (column : Fin 5) :
    iotaPhase 11 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 11 state) (Fin.ofNat 25 11)))[column] := by solve_iota_parities column

end Airbender.Keccak.Proofs
