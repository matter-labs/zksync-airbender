import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Rounds

/-- Parity calls 210–214 apply the delayed iota of round 14 and keep the other lanes. -/
theorem parity_lanes_14 (state : LaneState) :
    logicalLanes 14 (parityPhase 14 state) = iotaState (logicalLanes 14 state) 14 := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

/-- Parity call 210 writes Keccak's column parity C[0] (after the delayed iota). -/
theorem parity_column_zero_14 (state : LaneState) :
    parityPhase 14 state 25 = (thetaC (iotaState (logicalLanes 14 state) 14))[0] := by
  simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
