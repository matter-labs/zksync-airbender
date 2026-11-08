module
public import Slop.Keccak.PhaseDefinitions
public import Slop.Keccak.SlotReduction
public import Slop.KernelRfl
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

theorem chi_lanes_0 (state : LaneState) :
    logicalLanes 1 (chiPhase (0 : Fin 24) state) = chi (logicalLanes 1 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_1 (state : LaneState) :
    logicalLanes 2 (chiPhase (1 : Fin 24) state) = chi (logicalLanes 2 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_2 (state : LaneState) :
    logicalLanes 3 (chiPhase (2 : Fin 24) state) = chi (logicalLanes 3 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_3 (state : LaneState) :
    logicalLanes 4 (chiPhase (3 : Fin 24) state) = chi (logicalLanes 4 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_4 (state : LaneState) :
    logicalLanes 5 (chiPhase (4 : Fin 24) state) = chi (logicalLanes 5 state) := by
  simp only [chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals kernel_rfl


theorem chi_lanes_5 (state : LaneState) :
    logicalLanes 6 (chiPhase (5 : Fin 24) state) = chi (logicalLanes 6 state) := by
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
