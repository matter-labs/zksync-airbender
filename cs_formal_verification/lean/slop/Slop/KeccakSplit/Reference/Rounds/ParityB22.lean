import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Rounds

/-- Parity calls 331–334 write Keccak's column parities C[1..4]. -/
theorem parity_columns_22 (column : Fin 5) (nonzero : column ≠ 0) (state : LaneState) :
    parityPhase 22 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 22 state) 22))[column] := by
  fin_cases column
  · exact absurd rfl nonzero
  all_goals simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
