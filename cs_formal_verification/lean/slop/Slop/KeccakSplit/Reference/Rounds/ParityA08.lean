import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

namespace Rounds

/-- Parity calls 120–124 apply the delayed iota of round 8 and keep the other lanes. -/
theorem parity_lanes_8 (state : LaneState) :
    logicalLanes 8 (parityPhase 8 state) = iotaState (logicalLanes 8 state) 8 := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

/-- Parity call 120 writes Keccak's column parity C[0] (after the delayed iota). -/
theorem parity_column_zero_8 (state : LaneState) :
    parityPhase 8 state 25 = (thetaC (iotaState (logicalLanes 8 state) 8))[0] := by
  simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
