import Airbender.Proofs.Keccak.SplitSlotReduction
import Airbender.Proofs.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The second parity phase applies the original delayed round constant. -/
theorem parity_phase_round_one (state : LaneState) :
    logicalLanes 1 (parityPhase 1 state) =
      iotaState (logicalLanes 1 state) 1 ∧
    (∀ column : Fin 5, parityPhase 1 state ⟨25 + column.val, by omega⟩ =
      (thetaC (iotaState (logicalLanes 1 state) 1))[column]) := by
  constructor
  · apply Vector.ext
    intro lane bound
    interval_cases lane
    all_goals simp only [logicalLanes, Vector.getElem_ofFn, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
    all_goals rfl'
  · intro column
    fin_cases column
    all_goals simp only [logicalLanes, parityPhase,
      Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
      Airbender.Keccak.Proofs.physical_cached]
    all_goals rfl'

end Airbender.Keccak.Split.Call.Proofs
