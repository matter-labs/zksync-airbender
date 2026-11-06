import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

namespace Rounds

/-- Chi calls 235–239 apply Keccak's chi. -/
theorem chi_15 (state : LaneState) :
    logicalLanes (15 + 1) (chiPhase 15 state) = chi (logicalLanes (15 + 1) state) := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase,
    Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
    Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
