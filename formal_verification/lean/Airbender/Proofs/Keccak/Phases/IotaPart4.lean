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

namespace IotaPart4

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

/-- Four of the original per-round certificates, checked in a bounded compiler unit. -/
theorem lanes (round : Fin 4) (state : LaneState) :
    logicalLanes (16 + round.val)
      (iotaPhase ⟨16 + round.val, by omega⟩ state) =
      iotaState (logicalLanes (16 + round.val) state)
        (Fin.ofNat 25 (16 + round.val)) := by
  fin_cases round
  · exact lanes_16 state
  · exact lanes_17 state
  · exact lanes_18 state
  · exact lanes_19 state

theorem parities (round : Fin 4) (state : LaneState) (column : Fin 5) :
    iotaPhase ⟨16 + round.val, by omega⟩ state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes (16 + round.val) state)
        (Fin.ofNat 25 (16 + round.val))))[column] := by
  fin_cases round
  · exact parities_16 state column
  · exact parities_17 state column
  · exact parities_18 state column
  · exact parities_19 state column

end IotaPart4
end Airbender.Keccak.Proofs
