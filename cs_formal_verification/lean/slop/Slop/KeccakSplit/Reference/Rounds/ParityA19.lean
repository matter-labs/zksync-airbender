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

/-- Parity calls 285–289 apply the delayed iota of round 19 and keep the other lanes. -/
theorem parity_lanes_19 (state : LaneState) :
    logicalLanes 19 (parityPhase 19 state) = iotaState (logicalLanes 19 state) 19 := by
  apply Vector.ext
  intro lane bound
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

/-- Parity call 285 writes Keccak's column parity C[0] (after the delayed iota). -/
theorem parity_column_zero_19 (state : LaneState) :
    parityPhase 19 state 25 = (thetaC (iotaState (logicalLanes 19 state) 19))[0] := by
  simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
  all_goals rfl'

end Rounds
end Airbender.Keccak.Split.Call.Proofs
