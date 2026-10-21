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

theorem iota_lanes_12 (state : LaneState) :
    logicalLanes 12 (iotaPhase 12 state) =
      iotaState (logicalLanes 12 state) (Fin.ofNat 25 12) := by solve_iota_lanes
theorem iota_parities_12 (state : LaneState) (column : Fin 5) :
    iotaPhase 12 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 12 state) (Fin.ofNat 25 12)))[column] := by solve_iota_parities column
theorem iota_lanes_13 (state : LaneState) :
    logicalLanes 13 (iotaPhase 13 state) =
      iotaState (logicalLanes 13 state) (Fin.ofNat 25 13) := by solve_iota_lanes
theorem iota_parities_13 (state : LaneState) (column : Fin 5) :
    iotaPhase 13 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 13 state) (Fin.ofNat 25 13)))[column] := by solve_iota_parities column
theorem iota_lanes_14 (state : LaneState) :
    logicalLanes 14 (iotaPhase 14 state) =
      iotaState (logicalLanes 14 state) (Fin.ofNat 25 14) := by solve_iota_lanes
theorem iota_parities_14 (state : LaneState) (column : Fin 5) :
    iotaPhase 14 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 14 state) (Fin.ofNat 25 14)))[column] := by solve_iota_parities column
theorem iota_lanes_15 (state : LaneState) :
    logicalLanes 15 (iotaPhase 15 state) =
      iotaState (logicalLanes 15 state) (Fin.ofNat 25 15) := by solve_iota_lanes
theorem iota_parities_15 (state : LaneState) (column : Fin 5) :
    iotaPhase 15 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 15 state) (Fin.ofNat 25 15)))[column] := by solve_iota_parities column
theorem iota_lanes_16 (state : LaneState) :
    logicalLanes 16 (iotaPhase 16 state) =
      iotaState (logicalLanes 16 state) (Fin.ofNat 25 16) := by solve_iota_lanes
theorem iota_parities_16 (state : LaneState) (column : Fin 5) :
    iotaPhase 16 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 16 state) (Fin.ofNat 25 16)))[column] := by solve_iota_parities column
theorem iota_lanes_17 (state : LaneState) :
    logicalLanes 17 (iotaPhase 17 state) =
      iotaState (logicalLanes 17 state) (Fin.ofNat 25 17) := by solve_iota_lanes
theorem iota_parities_17 (state : LaneState) (column : Fin 5) :
    iotaPhase 17 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 17 state) (Fin.ofNat 25 17)))[column] := by solve_iota_parities column

end Airbender.Keccak.Proofs
