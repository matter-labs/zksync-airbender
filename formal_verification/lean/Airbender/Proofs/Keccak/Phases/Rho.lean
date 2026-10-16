import Airbender.Proofs.Keccak.PhaseDefinitions
import Airbender.Proofs.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

private theorem rho_part0 (part : Fin 4) (state : LaneState) :
    logicalLanes ((0 + part.val) + 1) (rhoPhase ⟨0 + part.val, by omega⟩ state) = rhoPi (logicalLanes (0 + part.val) state) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, rhoPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.rhoPi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem rho_part1 (part : Fin 4) (state : LaneState) :
    logicalLanes ((4 + part.val) + 1) (rhoPhase ⟨4 + part.val, by omega⟩ state) = rhoPi (logicalLanes (4 + part.val) state) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, rhoPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.rhoPi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem rho_part2 (part : Fin 4) (state : LaneState) :
    logicalLanes ((8 + part.val) + 1) (rhoPhase ⟨8 + part.val, by omega⟩ state) = rhoPi (logicalLanes (8 + part.val) state) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, rhoPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.rhoPi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem rho_part3 (part : Fin 4) (state : LaneState) :
    logicalLanes ((12 + part.val) + 1) (rhoPhase ⟨12 + part.val, by omega⟩ state) = rhoPi (logicalLanes (12 + part.val) state) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, rhoPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.rhoPi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem rho_part4 (part : Fin 4) (state : LaneState) :
    logicalLanes ((16 + part.val) + 1) (rhoPhase ⟨16 + part.val, by omega⟩ state) = rhoPi (logicalLanes (16 + part.val) state) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, rhoPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.rhoPi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

private theorem rho_part5 (part : Fin 4) (state : LaneState) :
    logicalLanes ((20 + part.val) + 1) (rhoPhase ⟨20 + part.val, by omega⟩ state) = rhoPi (logicalLanes (20 + part.val) state) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, rhoPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.rhoPi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

theorem rho_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (rhoPhase round state) = rhoPi (logicalLanes round.val state) := by
  fin_cases round
  · exact rho_part0 0 state
  · exact rho_part0 1 state
  · exact rho_part0 2 state
  · exact rho_part0 3 state
  · exact rho_part1 0 state
  · exact rho_part1 1 state
  · exact rho_part1 2 state
  · exact rho_part1 3 state
  · exact rho_part2 0 state
  · exact rho_part2 1 state
  · exact rho_part2 2 state
  · exact rho_part2 3 state
  · exact rho_part3 0 state
  · exact rho_part3 1 state
  · exact rho_part3 2 state
  · exact rho_part3 3 state
  · exact rho_part4 0 state
  · exact rho_part4 1 state
  · exact rho_part4 2 state
  · exact rho_part4 3 state
  · exact rho_part5 0 state
  · exact rho_part5 1 state
  · exact rho_part5 2 state
  · exact rho_part5 3 state

end Airbender.Keccak.Proofs
