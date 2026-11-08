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

/-- Parity calls 151–154 write Keccak's column parities C[1..4]. -/
theorem parity_columns_10 (column : Fin 5) (nonzero : column ≠ 0) (state : LaneState) :
    parityPhase 10 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 10 state) 10))[column] := by
  fin_cases column
  · exact absurd rfl nonzero
  all_goals simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
