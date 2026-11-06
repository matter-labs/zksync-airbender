import Slop.Keccak.PhaseDefinitions
import Slop.Keccak.SlotReduction
import Slop.KernelRfl

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

theorem chi_lanes_18 (state : LaneState) :
    logicalLanes 19 (chiPhase (18 : Fin 24) state) = chi (logicalLanes 19 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_19 (state : LaneState) :
    logicalLanes 20 (chiPhase (19 : Fin 24) state) = chi (logicalLanes 20 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_20 (state : LaneState) :
    logicalLanes 21 (chiPhase (20 : Fin 24) state) = chi (logicalLanes 21 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_21 (state : LaneState) :
    logicalLanes 22 (chiPhase (21 : Fin 24) state) = chi (logicalLanes 22 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_22 (state : LaneState) :
    logicalLanes 23 (chiPhase (22 : Fin 24) state) = chi (logicalLanes 23 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_23 (state : LaneState) :
    logicalLanes 24 (chiPhase (23 : Fin 24) state) = chi (logicalLanes 24 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl

end Airbender.Keccak.Proofs
