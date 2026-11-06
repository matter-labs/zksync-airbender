import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536

namespace Rounds

/-- Parity calls 270–274 apply the delayed iota of round 18 and keep the other lanes. -/
theorem parity_lanes_18 (state : LaneState) :
    logicalLanes 18 (parityPhase 18 state) = iotaState (logicalLanes 18 state) 18 := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

/-- Parity call 270 writes Keccak's column parity C[0] (after the delayed iota). -/
theorem parity_column_zero_18 (state : LaneState) :
    parityPhase 18 state 25 = (thetaC (iotaState (logicalLanes 18 state) 18))[0] := by
  simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
