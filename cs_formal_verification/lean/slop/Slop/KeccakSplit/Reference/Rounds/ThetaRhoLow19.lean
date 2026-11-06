import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 2000000
attribute [local cbv_opaque] rotLeft64 not64 Nat.xor Nat.land roundConstants

namespace Rounds

/-- Theta+rho calls 290–294 apply Keccak's theta and rho (and rename by pi): lanes 0–12. -/
theorem thetaRho_low_19 (state : LaneState) (lane : Nat) (bound : lane < 13) :
    (logicalLanes (19 + 1) (thetaRhoPhase 19 state))[lane] =
      (rhoPi (thetaXor (logicalLanes 19 state)
        (thetaD (Vector.ofFn fun column : Fin 5 => state ⟨25 + column.val, by omega⟩))))[lane] := by
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaRhoPhase,
    Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
    Airbender.Keccak.Proofs.physical_cached]
  all_goals cbv

end Rounds
end Airbender.Keccak.Split.Call.Proofs
