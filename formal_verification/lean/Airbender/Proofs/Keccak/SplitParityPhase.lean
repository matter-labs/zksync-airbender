import Airbender.Proofs.Keccak.SplitPermutationDefinitions

namespace Airbender.Keccak.Split.Call.Proofs
open Specs.Keccak256
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 2000000
attribute [local cbv_opaque] rotLeft64 not64 Nat.xor Nat.land roundConstants

/-- The first five split calls produce the exact delayed-iota column parity. -/
theorem parity_phase_round_zero (state : LaneState) :
    logicalLanes 0 (parityPhase 0 state) = logicalLanes 0 state ∧
    (∀ column : Fin 5, parityPhase 0 state ⟨25 + column.val, by omega⟩ =
      (thetaC (logicalLanes 0 state))[column]) := by
  constructor
  · apply Vector.ext
    intro lane bound
    interval_cases lane <;> cbv
    change state 0 ^^^ 0 = state 0
    exact Nat.xor_zero _
  · intro column
    fin_cases column <;> cbv
    change (((((state 0 ^^^ 0) ^^^ state 5) ^^^ state 10) ^^^ state 15) ^^^ state 20) =
      ((((state 0 ^^^ state 5) ^^^ state 10) ^^^ state 15) ^^^ state 20)
    rw [Nat.xor_zero]

end Airbender.Keccak.Split.Call.Proofs
