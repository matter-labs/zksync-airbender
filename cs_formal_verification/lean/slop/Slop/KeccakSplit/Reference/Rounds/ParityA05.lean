import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

namespace Rounds

/-- Parity calls 75–79 apply the delayed iota of round 5 and keep the other lanes. -/
theorem parity_lanes_5 (state : LaneState) :
    logicalLanes 5 (parityPhase 5 state) = iotaState (logicalLanes 5 state) 5 := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

/-- Parity call 75 writes Keccak's column parity C[0] (after the delayed iota). -/
theorem parity_column_zero_5 (state : LaneState) :
    parityPhase 5 state 25 = (thetaC (iotaState (logicalLanes 5 state) 5))[0] := by
  simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
