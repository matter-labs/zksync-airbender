import Airbender.Proofs.Keccak.SplitSlotReduction
import Airbender.Proofs.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 2000000
attribute [local cbv_opaque] rotLeft64 not64 Nat.xor Nat.land roundConstants

namespace ThetaRhoPart5.First

/-- Two split phases match the unchanged original Keccak reference. -/
theorem reference (part : Fin 2) (state : LaneState) :
    logicalLanes (20 + part.val + 1)
      (thetaRhoPhase ⟨20 + part.val, by omega⟩ state) =
      rhoPi (thetaXor (logicalLanes (20 + part.val) state)
        (thetaD (Vector.ofFn fun column : Fin 5 => state ⟨25 + column.val, by omega⟩))) := by
  apply Vector.ext
  intro lane bound
  fin_cases part
  all_goals interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaRhoPhase,
    Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
    Airbender.Keccak.Proofs.physical_cached]
  all_goals cbv

end ThetaRhoPart5.First
end Airbender.Keccak.Split.Call.Proofs
