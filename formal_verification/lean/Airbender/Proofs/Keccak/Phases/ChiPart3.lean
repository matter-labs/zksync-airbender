import Airbender.Proofs.Keccak.PhaseDefinitions
import Airbender.Proofs.Keccak.SlotReduction

namespace Airbender.Keccak.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 64000000

namespace ChiPart3

theorem lanes (part : Fin 4) (state : LaneState) :
    logicalLanes ((12 + part.val) + 1) (chiPhase ⟨12 + part.val, by omega⟩ state) = chi (logicalLanes ((12 + part.val) + 1) state) := by
  apply Vector.ext
  intro i bound
  fin_cases part
  all_goals interval_cases i
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase, Fin.foldl_succ_last, Fin.foldl_zero]
  all_goals norm_num only [Specs.Keccak256.chi, Fin.getElem_fin, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp only [physical_cached, micro_normalized]
  all_goals rfl'

end ChiPart3

end Airbender.Keccak.Proofs
