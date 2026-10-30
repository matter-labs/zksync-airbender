import Airbender.Proofs.Keccak.SplitSlotReduction
import Airbender.Proofs.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace ChiPart2

/-- Four split phases match the unchanged original Keccak reference. -/
theorem reference (part : Fin 4) (state : LaneState) :
    logicalLanes (8 + part.val + 1)
      (chiPhase ⟨8 + part.val, by omega⟩ state) =
      chi (logicalLanes (8 + part.val + 1) state) := by
  apply Vector.ext
  intro lane bound
  fin_cases part
  all_goals interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase,
    Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
    Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end ChiPart2
end Airbender.Keccak.Split.Call.Proofs
