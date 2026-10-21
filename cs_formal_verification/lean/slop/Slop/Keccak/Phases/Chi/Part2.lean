import Slop.Keccak.PhaseDefinitions
import Slop.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

theorem chi_lanes_12 (state : LaneState) :
    logicalLanes 13 (chiPhase (12 : Fin 24) state) = chi (logicalLanes 13 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_13 (state : LaneState) :
    logicalLanes 14 (chiPhase (13 : Fin 24) state) = chi (logicalLanes 14 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_14 (state : LaneState) :
    logicalLanes 15 (chiPhase (14 : Fin 24) state) = chi (logicalLanes 15 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_15 (state : LaneState) :
    logicalLanes 16 (chiPhase (15 : Fin 24) state) = chi (logicalLanes 16 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_16 (state : LaneState) :
    logicalLanes 17 (chiPhase (16 : Fin 24) state) = chi (logicalLanes 17 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'


theorem chi_lanes_17 (state : LaneState) :
    logicalLanes 18 (chiPhase (17 : Fin 24) state) = chi (logicalLanes 18 state) := by
  apply Vector.ext
  intro i bound
  interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

end Airbender.Keccak.Proofs
