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

namespace IotaPart0

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

/-- Four of the original per-round certificates, checked in a bounded compiler unit. -/
theorem lanes (round : Fin 4) (state : LaneState) :
    logicalLanes (0 + round.val)
      (iotaPhase ⟨0 + round.val, by omega⟩ state) =
      iotaState (logicalLanes (0 + round.val) state)
        (Fin.ofNat 25 (0 + round.val)) := by
  fin_cases round
  · exact lanes_0 state
  · exact lanes_1 state
  · exact lanes_2 state
  · exact lanes_3 state

theorem parities (round : Fin 4) (state : LaneState) (column : Fin 5) :
    iotaPhase ⟨0 + round.val, by omega⟩ state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes (0 + round.val) state)
        (Fin.ofNat 25 (0 + round.val))))[column] := by
  fin_cases round
  · exact parities_0 state column
  · exact parities_1 state column
  · exact parities_2 state column
  · exact parities_3 state column

end IotaPart0
end Airbender.Keccak.Proofs
