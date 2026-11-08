module
public import Slop.KeccakSplit.Reference.SlotReduction
public import Slop.Keccak.LayoutReduction
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

namespace Rounds

/-- Chi calls 85–89 apply Keccak's chi. -/
theorem chi_5 (state : LaneState) :
    logicalLanes (5 + 1) (chiPhase 5 state) = chi (logicalLanes (5 + 1) state) := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, chiPhase,
    Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
    Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
