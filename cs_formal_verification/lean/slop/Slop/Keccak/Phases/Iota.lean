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

private theorem lanes_0 (state : LaneState) :
    logicalLanes 0 (iotaPhase 0 state) =
      iotaState (logicalLanes 0 state) (Fin.ofNat 25 0) := by solve_iota_lanes
private theorem parities_0 (state : LaneState) (column : Fin 5) :
    iotaPhase 0 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 0 state) (Fin.ofNat 25 0)))[column] := by solve_iota_parities column
private theorem lanes_1 (state : LaneState) :
    logicalLanes 1 (iotaPhase 1 state) =
      iotaState (logicalLanes 1 state) (Fin.ofNat 25 1) := by solve_iota_lanes
private theorem parities_1 (state : LaneState) (column : Fin 5) :
    iotaPhase 1 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 1 state) (Fin.ofNat 25 1)))[column] := by solve_iota_parities column
private theorem lanes_2 (state : LaneState) :
    logicalLanes 2 (iotaPhase 2 state) =
      iotaState (logicalLanes 2 state) (Fin.ofNat 25 2) := by solve_iota_lanes
private theorem parities_2 (state : LaneState) (column : Fin 5) :
    iotaPhase 2 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 2 state) (Fin.ofNat 25 2)))[column] := by solve_iota_parities column
private theorem lanes_3 (state : LaneState) :
    logicalLanes 3 (iotaPhase 3 state) =
      iotaState (logicalLanes 3 state) (Fin.ofNat 25 3) := by solve_iota_lanes
private theorem parities_3 (state : LaneState) (column : Fin 5) :
    iotaPhase 3 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 3 state) (Fin.ofNat 25 3)))[column] := by solve_iota_parities column
private theorem lanes_4 (state : LaneState) :
    logicalLanes 4 (iotaPhase 4 state) =
      iotaState (logicalLanes 4 state) (Fin.ofNat 25 4) := by solve_iota_lanes
private theorem parities_4 (state : LaneState) (column : Fin 5) :
    iotaPhase 4 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 4 state) (Fin.ofNat 25 4)))[column] := by solve_iota_parities column
private theorem lanes_5 (state : LaneState) :
    logicalLanes 5 (iotaPhase 5 state) =
      iotaState (logicalLanes 5 state) (Fin.ofNat 25 5) := by solve_iota_lanes
private theorem parities_5 (state : LaneState) (column : Fin 5) :
    iotaPhase 5 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 5 state) (Fin.ofNat 25 5)))[column] := by solve_iota_parities column
private theorem lanes_6 (state : LaneState) :
    logicalLanes 6 (iotaPhase 6 state) =
      iotaState (logicalLanes 6 state) (Fin.ofNat 25 6) := by solve_iota_lanes
private theorem parities_6 (state : LaneState) (column : Fin 5) :
    iotaPhase 6 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 6 state) (Fin.ofNat 25 6)))[column] := by solve_iota_parities column
private theorem lanes_7 (state : LaneState) :
    logicalLanes 7 (iotaPhase 7 state) =
      iotaState (logicalLanes 7 state) (Fin.ofNat 25 7) := by solve_iota_lanes
private theorem parities_7 (state : LaneState) (column : Fin 5) :
    iotaPhase 7 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 7 state) (Fin.ofNat 25 7)))[column] := by solve_iota_parities column
private theorem lanes_8 (state : LaneState) :
    logicalLanes 8 (iotaPhase 8 state) =
      iotaState (logicalLanes 8 state) (Fin.ofNat 25 8) := by solve_iota_lanes
private theorem parities_8 (state : LaneState) (column : Fin 5) :
    iotaPhase 8 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 8 state) (Fin.ofNat 25 8)))[column] := by solve_iota_parities column
private theorem lanes_9 (state : LaneState) :
    logicalLanes 9 (iotaPhase 9 state) =
      iotaState (logicalLanes 9 state) (Fin.ofNat 25 9) := by solve_iota_lanes
private theorem parities_9 (state : LaneState) (column : Fin 5) :
    iotaPhase 9 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 9 state) (Fin.ofNat 25 9)))[column] := by solve_iota_parities column
private theorem lanes_10 (state : LaneState) :
    logicalLanes 10 (iotaPhase 10 state) =
      iotaState (logicalLanes 10 state) (Fin.ofNat 25 10) := by solve_iota_lanes
private theorem parities_10 (state : LaneState) (column : Fin 5) :
    iotaPhase 10 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 10 state) (Fin.ofNat 25 10)))[column] := by solve_iota_parities column
private theorem lanes_11 (state : LaneState) :
    logicalLanes 11 (iotaPhase 11 state) =
      iotaState (logicalLanes 11 state) (Fin.ofNat 25 11) := by solve_iota_lanes
private theorem parities_11 (state : LaneState) (column : Fin 5) :
    iotaPhase 11 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 11 state) (Fin.ofNat 25 11)))[column] := by solve_iota_parities column
private theorem lanes_12 (state : LaneState) :
    logicalLanes 12 (iotaPhase 12 state) =
      iotaState (logicalLanes 12 state) (Fin.ofNat 25 12) := by solve_iota_lanes
private theorem parities_12 (state : LaneState) (column : Fin 5) :
    iotaPhase 12 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 12 state) (Fin.ofNat 25 12)))[column] := by solve_iota_parities column
private theorem lanes_13 (state : LaneState) :
    logicalLanes 13 (iotaPhase 13 state) =
      iotaState (logicalLanes 13 state) (Fin.ofNat 25 13) := by solve_iota_lanes
private theorem parities_13 (state : LaneState) (column : Fin 5) :
    iotaPhase 13 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 13 state) (Fin.ofNat 25 13)))[column] := by solve_iota_parities column
private theorem lanes_14 (state : LaneState) :
    logicalLanes 14 (iotaPhase 14 state) =
      iotaState (logicalLanes 14 state) (Fin.ofNat 25 14) := by solve_iota_lanes
private theorem parities_14 (state : LaneState) (column : Fin 5) :
    iotaPhase 14 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 14 state) (Fin.ofNat 25 14)))[column] := by solve_iota_parities column
private theorem lanes_15 (state : LaneState) :
    logicalLanes 15 (iotaPhase 15 state) =
      iotaState (logicalLanes 15 state) (Fin.ofNat 25 15) := by solve_iota_lanes
private theorem parities_15 (state : LaneState) (column : Fin 5) :
    iotaPhase 15 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 15 state) (Fin.ofNat 25 15)))[column] := by solve_iota_parities column
private theorem lanes_16 (state : LaneState) :
    logicalLanes 16 (iotaPhase 16 state) =
      iotaState (logicalLanes 16 state) (Fin.ofNat 25 16) := by solve_iota_lanes
private theorem parities_16 (state : LaneState) (column : Fin 5) :
    iotaPhase 16 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 16 state) (Fin.ofNat 25 16)))[column] := by solve_iota_parities column
private theorem lanes_17 (state : LaneState) :
    logicalLanes 17 (iotaPhase 17 state) =
      iotaState (logicalLanes 17 state) (Fin.ofNat 25 17) := by solve_iota_lanes
private theorem parities_17 (state : LaneState) (column : Fin 5) :
    iotaPhase 17 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 17 state) (Fin.ofNat 25 17)))[column] := by solve_iota_parities column
private theorem lanes_18 (state : LaneState) :
    logicalLanes 18 (iotaPhase 18 state) =
      iotaState (logicalLanes 18 state) (Fin.ofNat 25 18) := by solve_iota_lanes
private theorem parities_18 (state : LaneState) (column : Fin 5) :
    iotaPhase 18 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 18 state) (Fin.ofNat 25 18)))[column] := by solve_iota_parities column
private theorem lanes_19 (state : LaneState) :
    logicalLanes 19 (iotaPhase 19 state) =
      iotaState (logicalLanes 19 state) (Fin.ofNat 25 19) := by solve_iota_lanes
private theorem parities_19 (state : LaneState) (column : Fin 5) :
    iotaPhase 19 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 19 state) (Fin.ofNat 25 19)))[column] := by solve_iota_parities column
private theorem lanes_20 (state : LaneState) :
    logicalLanes 20 (iotaPhase 20 state) =
      iotaState (logicalLanes 20 state) (Fin.ofNat 25 20) := by solve_iota_lanes
private theorem parities_20 (state : LaneState) (column : Fin 5) :
    iotaPhase 20 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 20 state) (Fin.ofNat 25 20)))[column] := by solve_iota_parities column
private theorem lanes_21 (state : LaneState) :
    logicalLanes 21 (iotaPhase 21 state) =
      iotaState (logicalLanes 21 state) (Fin.ofNat 25 21) := by solve_iota_lanes
private theorem parities_21 (state : LaneState) (column : Fin 5) :
    iotaPhase 21 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 21 state) (Fin.ofNat 25 21)))[column] := by solve_iota_parities column
private theorem lanes_22 (state : LaneState) :
    logicalLanes 22 (iotaPhase 22 state) =
      iotaState (logicalLanes 22 state) (Fin.ofNat 25 22) := by solve_iota_lanes
private theorem parities_22 (state : LaneState) (column : Fin 5) :
    iotaPhase 22 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 22 state) (Fin.ofNat 25 22)))[column] := by solve_iota_parities column
private theorem lanes_23 (state : LaneState) :
    logicalLanes 23 (iotaPhase 23 state) =
      iotaState (logicalLanes 23 state) (Fin.ofNat 25 23) := by solve_iota_lanes
private theorem parities_23 (state : LaneState) (column : Fin 5) :
    iotaPhase 23 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 23 state) (Fin.ofNat 25 23)))[column] := by solve_iota_parities column

theorem iota_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (iotaPhase round state) =
      iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val) := by
  fin_cases round
  · exact lanes_0 state
  · exact lanes_1 state
  · exact lanes_2 state
  · exact lanes_3 state
  · exact lanes_4 state
  · exact lanes_5 state
  · exact lanes_6 state
  · exact lanes_7 state
  · exact lanes_8 state
  · exact lanes_9 state
  · exact lanes_10 state
  · exact lanes_11 state
  · exact lanes_12 state
  · exact lanes_13 state
  · exact lanes_14 state
  · exact lanes_15 state
  · exact lanes_16 state
  · exact lanes_17 state
  · exact lanes_18 state
  · exact lanes_19 state
  · exact lanes_20 state
  · exact lanes_21 state
  · exact lanes_22 state
  · exact lanes_23 state

theorem iota_phase_parities (round : Fin 24) (state : LaneState) (column : Fin 5) :
    iotaPhase round state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes round.val state) (Fin.ofNat 25 round.val)))[column] := by
  fin_cases round
  · exact parities_0 state column
  · exact parities_1 state column
  · exact parities_2 state column
  · exact parities_3 state column
  · exact parities_4 state column
  · exact parities_5 state column
  · exact parities_6 state column
  · exact parities_7 state column
  · exact parities_8 state column
  · exact parities_9 state column
  · exact parities_10 state column
  · exact parities_11 state column
  · exact parities_12 state column
  · exact parities_13 state column
  · exact parities_14 state column
  · exact parities_15 state column
  · exact parities_16 state column
  · exact parities_17 state column
  · exact parities_18 state column
  · exact parities_19 state column
  · exact parities_20 state column
  · exact parities_21 state column
  · exact parities_22 state column
  · exact parities_23 state column

end Airbender.Keccak.Proofs
