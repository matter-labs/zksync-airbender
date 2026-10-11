import Airbender.Proofs.Keccak.PhaseDefinitions
import Airbender.Proofs.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

theorem chi_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (chiPhase round state) = chi (logicalLanes (round.val + 1) state) := by
  apply Vector.ext
  intro i bound
  fin_cases round
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

end Airbender.Keccak.Proofs
