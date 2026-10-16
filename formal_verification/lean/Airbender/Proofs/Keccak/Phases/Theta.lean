import Airbender.Proofs.Keccak.PhaseDefinitions
import Airbender.Proofs.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

private theorem theta_part0 (part : Fin 4) (state : LaneState) :
    logicalLanes (0 + part.val) (thetaPhase ⟨0 + part.val, by omega⟩ state) =
      thetaXor (logicalLanes (0 + part.val) state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.thetaXor, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem theta_part1 (part : Fin 4) (state : LaneState) :
    logicalLanes (4 + part.val) (thetaPhase ⟨4 + part.val, by omega⟩ state) =
      thetaXor (logicalLanes (4 + part.val) state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.thetaXor, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem theta_part2 (part : Fin 4) (state : LaneState) :
    logicalLanes (8 + part.val) (thetaPhase ⟨8 + part.val, by omega⟩ state) =
      thetaXor (logicalLanes (8 + part.val) state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.thetaXor, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem theta_part3 (part : Fin 4) (state : LaneState) :
    logicalLanes (12 + part.val) (thetaPhase ⟨12 + part.val, by omega⟩ state) =
      thetaXor (logicalLanes (12 + part.val) state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.thetaXor, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem theta_part4 (part : Fin 4) (state : LaneState) :
    logicalLanes (16 + part.val) (thetaPhase ⟨16 + part.val, by omega⟩ state) =
      thetaXor (logicalLanes (16 + part.val) state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.thetaXor, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem theta_part5 (part : Fin 4) (state : LaneState) :
    logicalLanes (20 + part.val) (thetaPhase ⟨20 + part.val, by omega⟩ state) =
      thetaXor (logicalLanes (20 + part.val) state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.thetaXor, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

theorem theta_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (thetaPhase round state) =
      thetaXor (logicalLanes round.val state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  fin_cases round
  · exact theta_part0 0 state
  · exact theta_part0 1 state
  · exact theta_part0 2 state
  · exact theta_part0 3 state
  · exact theta_part1 0 state
  · exact theta_part1 1 state
  · exact theta_part1 2 state
  · exact theta_part1 3 state
  · exact theta_part2 0 state
  · exact theta_part2 1 state
  · exact theta_part2 2 state
  · exact theta_part2 3 state
  · exact theta_part3 0 state
  · exact theta_part3 1 state
  · exact theta_part3 2 state
  · exact theta_part3 3 state
  · exact theta_part4 0 state
  · exact theta_part4 1 state
  · exact theta_part4 2 state
  · exact theta_part4 3 state
  · exact theta_part5 0 state
  · exact theta_part5 1 state
  · exact theta_part5 2 state
  · exact theta_part5 3 state

end Airbender.Keccak.Proofs
