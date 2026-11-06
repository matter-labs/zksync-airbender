import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

namespace Rounds

/-- Parity calls 241–244 write Keccak's column parities C[1..4]. -/
theorem parity_columns_16 (column : Fin 5) (nonzero : column ≠ 0) (state : LaneState) :
    parityPhase 16 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 16 state) 16))[column] := by
  fin_cases column
  · exact absurd rfl nonzero
  all_goals simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
