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

namespace IotaPart3

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

/-- Four of the original per-round certificates, checked in a bounded compiler unit. -/
theorem lanes (round : Fin 4) (state : LaneState) :
    logicalLanes (12 + round.val)
      (iotaPhase ⟨12 + round.val, by omega⟩ state) =
      iotaState (logicalLanes (12 + round.val) state)
        (Fin.ofNat 25 (12 + round.val)) := by
  fin_cases round
  · exact lanes_12 state
  · exact lanes_13 state
  · exact lanes_14 state
  · exact lanes_15 state

theorem parities (round : Fin 4) (state : LaneState) (column : Fin 5) :
    iotaPhase ⟨12 + round.val, by omega⟩ state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes (12 + round.val) state)
        (Fin.ofNat 25 (12 + round.val))))[column] := by
  fin_cases round
  · exact parities_12 state column
  · exact parities_13 state column
  · exact parities_14 state column
  · exact parities_15 state column

end IotaPart3
end Airbender.Keccak.Proofs
