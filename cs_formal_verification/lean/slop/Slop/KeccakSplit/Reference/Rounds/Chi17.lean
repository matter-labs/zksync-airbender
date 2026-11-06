import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Rounds

/-- Chi calls 265–269 apply Keccak's chi. -/
theorem chi_17 (state : LaneState) :
    logicalLanes (17 + 1) (chiPhase 17 state) = chi (logicalLanes (17 + 1) state) := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase,
    Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
    Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
