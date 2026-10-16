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

namespace IotaPart1

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

/-- Four of the original per-round certificates, checked in a bounded compiler unit. -/
theorem lanes (round : Fin 4) (state : LaneState) :
    logicalLanes (4 + round.val)
      (iotaPhase ⟨4 + round.val, by omega⟩ state) =
      iotaState (logicalLanes (4 + round.val) state)
        (Fin.ofNat 25 (4 + round.val)) := by
  fin_cases round
  · exact lanes_4 state
  · exact lanes_5 state
  · exact lanes_6 state
  · exact lanes_7 state

theorem parities (round : Fin 4) (state : LaneState) (column : Fin 5) :
    iotaPhase ⟨4 + round.val, by omega⟩ state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes (4 + round.val) state)
        (Fin.ofNat 25 (4 + round.val))))[column] := by
  fin_cases round
  · exact parities_4 state column
  · exact parities_5 state column
  · exact parities_6 state column
  · exact parities_7 state column

end IotaPart1
end Airbender.Keccak.Proofs
