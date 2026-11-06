import Slop.KeccakSplit.Reference.SlotReduction
import Slop.Keccak.LayoutReduction

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option cbv.maxSteps 2000000
attribute [local cbv_opaque] rotLeft64 not64 Nat.xor Nat.land roundConstants

namespace Rounds

/-- Theta+rho calls 320–324 apply Keccak's theta and rho (and rename by pi): lanes 13–24. -/
theorem thetaRho_high_21 (state : LaneState) (lane : Nat) (low : 13 ≤ lane) (bound : lane < 25) :
    (logicalLanes (21 + 1) (thetaRhoPhase 21 state))[lane] =
      (rhoPi (thetaXor (logicalLanes 21 state)
        (thetaD (Vector.ofFn fun column : Fin 5 => state ⟨25 + column.val, by omega⟩))))[lane] := by
  interval_cases lane
  all_goals simp only [logicalLanes, Vector.getElem_ofFn, thetaRhoPhase,
    Fin.foldl_succ_last, Fin.foldl_zero, micro_normalized,
    Airbender.Keccak.Proofs.physical_cached]
  all_goals cbv

end Rounds
end Airbender.Keccak.Split.Call.Proofs
