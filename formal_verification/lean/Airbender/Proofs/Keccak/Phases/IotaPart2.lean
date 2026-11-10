import Airbender.Proofs.Keccak.PhaseDefinitions
import Airbender.Proofs.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option Elab.async false
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

namespace IotaPart2

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

/-- Four of the original per-round certificates, checked in a bounded compiler unit. -/
theorem lanes (round : Fin 4) (state : LaneState) :
    logicalLanes (8 + round.val)
      (iotaPhase ⟨8 + round.val, by omega⟩ state) =
      iotaState (logicalLanes (8 + round.val) state)
        (Fin.ofNat 25 (8 + round.val)) := by
  fin_cases round
  · exact lanes_8 state
  · exact lanes_9 state
  · exact lanes_10 state
  · exact lanes_11 state

theorem parities (round : Fin 4) (state : LaneState) (column : Fin 5) :
    iotaPhase ⟨8 + round.val, by omega⟩ state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes (8 + round.val) state)
        (Fin.ofNat 25 (8 + round.val))))[column] := by
  fin_cases round
  · exact parities_8 state column
  · exact parities_9 state column
  · exact parities_10 state column
  · exact parities_11 state column

end IotaPart2
end Airbender.Keccak.Proofs
