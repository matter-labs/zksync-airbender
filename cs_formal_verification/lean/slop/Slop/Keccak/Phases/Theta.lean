import Slop.Keccak.PhaseDefinitions
import Slop.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

theorem theta_phase_lanes (round : Fin 24) (state : LaneState) :
    logicalLanes round.val (thetaPhase round state) =
      thetaXor (logicalLanes round.val state)
        (Vector.ofFn fun i : Fin 5 => state ⟨25 + (i.val + 4) % 5,
          by have := Nat.mod_lt (i.val + 4) (by decide : 0 < 5); omega⟩) := by
  apply Vector.ext
  intro i bound
  fin_cases round
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.thetaXor, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

end Airbender.Keccak.Proofs
