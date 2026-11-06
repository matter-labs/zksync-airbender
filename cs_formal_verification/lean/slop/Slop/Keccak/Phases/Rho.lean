import Slop.Keccak.PhaseDefinitions
import Slop.Keccak.SlotReduction
import Slop.DeferredRfl

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

theorem rho_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes (round.val + 1) (rhoPhase round state) = rhoPi (logicalLanes round.val state) := by
  fin_cases round
  all_goals simp only [rhoPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals apply Vector.ext
  all_goals intro i bound
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn]
  all_goals norm_num only [Specs.Keccak256.rhoPi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals deferred_rfl

end Airbender.Keccak.Proofs
