import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

namespace Rounds

/-- Parity calls 30–34 apply the delayed iota of round 2 and keep the other lanes. -/
theorem parity_lanes_2 (state : LaneState) :
    logicalLanes 2 (parityPhase 2 state) = iotaState (logicalLanes 2 state) 2 := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

/-- Parity call 30 writes Keccak's column parity C[0] (after the delayed iota). -/
theorem parity_column_zero_2 (state : LaneState) :
    parityPhase 2 state 25 = (thetaC (iotaState (logicalLanes 2 state) 2))[0] := by
  simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
