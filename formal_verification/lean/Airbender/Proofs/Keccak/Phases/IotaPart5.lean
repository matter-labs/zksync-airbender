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

namespace IotaPart5

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

/-- Four of the original per-round certificates, checked in a bounded compiler unit. -/
theorem lanes (round : Fin 4) (state : LaneState) :
    logicalLanes (20 + round.val)
      (iotaPhase ⟨20 + round.val, by omega⟩ state) =
      iotaState (logicalLanes (20 + round.val) state)
        (Fin.ofNat 25 (20 + round.val)) := by
  fin_cases round
  · exact lanes_20 state
  · exact lanes_21 state
  · exact lanes_22 state
  · exact lanes_23 state

theorem parities (round : Fin 4) (state : LaneState) (column : Fin 5) :
    iotaPhase ⟨20 + round.val, by omega⟩ state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes (20 + round.val) state)
        (Fin.ofNat 25 (20 + round.val))))[column] := by
  fin_cases round
  · exact parities_20 state column
  · exact parities_21 state column
  · exact parities_22 state column
  · exact parities_23 state column

end IotaPart5
end Airbender.Keccak.Proofs
