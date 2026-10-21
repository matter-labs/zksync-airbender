import Slop.Keccak.PhaseDefinitions
import Slop.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

theorem chi_lanes_0 (state : LaneState) :
    logicalLanes 1 (chiPhase (0 : Fin 24) state) = chi (logicalLanes 1 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_1 (state : LaneState) :
    logicalLanes 2 (chiPhase (1 : Fin 24) state) = chi (logicalLanes 2 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_2 (state : LaneState) :
    logicalLanes 3 (chiPhase (2 : Fin 24) state) = chi (logicalLanes 3 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_3 (state : LaneState) :
    logicalLanes 4 (chiPhase (3 : Fin 24) state) = chi (logicalLanes 4 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_4 (state : LaneState) :
    logicalLanes 5 (chiPhase (4 : Fin 24) state) = chi (logicalLanes 5 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_5 (state : LaneState) :
    logicalLanes 6 (chiPhase (5 : Fin 24) state) = chi (logicalLanes 6 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

end Airbender.Keccak.Proofs
