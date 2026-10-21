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

theorem iota_lanes_18 (state : LaneState) :
    logicalLanes 18 (iotaPhase 18 state) =
      iotaState (logicalLanes 18 state) (Fin.ofNat 25 18) := by solve_iota_lanes
theorem iota_parities_18 (state : LaneState) (column : Fin 5) :
    iotaPhase 18 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 18 state) (Fin.ofNat 25 18)))[column] := by solve_iota_parities column
theorem iota_lanes_19 (state : LaneState) :
    logicalLanes 19 (iotaPhase 19 state) =
      iotaState (logicalLanes 19 state) (Fin.ofNat 25 19) := by solve_iota_lanes
theorem iota_parities_19 (state : LaneState) (column : Fin 5) :
    iotaPhase 19 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 19 state) (Fin.ofNat 25 19)))[column] := by solve_iota_parities column
theorem iota_lanes_20 (state : LaneState) :
    logicalLanes 20 (iotaPhase 20 state) =
      iotaState (logicalLanes 20 state) (Fin.ofNat 25 20) := by solve_iota_lanes
theorem iota_parities_20 (state : LaneState) (column : Fin 5) :
    iotaPhase 20 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 20 state) (Fin.ofNat 25 20)))[column] := by solve_iota_parities column
theorem iota_lanes_21 (state : LaneState) :
    logicalLanes 21 (iotaPhase 21 state) =
      iotaState (logicalLanes 21 state) (Fin.ofNat 25 21) := by solve_iota_lanes
theorem iota_parities_21 (state : LaneState) (column : Fin 5) :
    iotaPhase 21 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 21 state) (Fin.ofNat 25 21)))[column] := by solve_iota_parities column
theorem iota_lanes_22 (state : LaneState) :
    logicalLanes 22 (iotaPhase 22 state) =
      iotaState (logicalLanes 22 state) (Fin.ofNat 25 22) := by solve_iota_lanes
theorem iota_parities_22 (state : LaneState) (column : Fin 5) :
    iotaPhase 22 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 22 state) (Fin.ofNat 25 22)))[column] := by solve_iota_parities column
theorem iota_lanes_23 (state : LaneState) :
    logicalLanes 23 (iotaPhase 23 state) =
      iotaState (logicalLanes 23 state) (Fin.ofNat 25 23) := by solve_iota_lanes
theorem iota_parities_23 (state : LaneState) (column : Fin 5) :
    iotaPhase 23 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 23 state) (Fin.ofNat 25 23)))[column] := by solve_iota_parities column

end Airbender.Keccak.Proofs
