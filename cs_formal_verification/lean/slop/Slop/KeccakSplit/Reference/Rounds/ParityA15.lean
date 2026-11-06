import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Rounds

/-- Parity calls 225–229 apply the delayed iota of round 15 and keep the other lanes. -/
theorem parity_lanes_15 (state : LaneState) :
    logicalLanes 15 (parityPhase 15 state) = iotaState (logicalLanes 15 state) 15 := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

/-- Parity call 225 writes Keccak's column parity C[0] (after the delayed iota). -/
theorem parity_column_zero_15 (state : LaneState) :
    parityPhase 15 state 25 = (thetaC (iotaState (logicalLanes 15 state) 15))[0] := by
  simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
