import Airbender.Proofs.Blake2Round.NativeFinalBDBindings
import Airbender.Proofs.Blake2Round.NativeFinalQueryBase

namespace Airbender.Blake2Round.Proofs
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem native_bd_queries_cached {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (limb : Fin 8) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w limb) (bdTemp w limb 0) (bdTemp w limb 1) ∧
    chunkXor 7 (bdHighB w limb)
      ((-3932160 : ZMod p) * (bdInitial w limb - bdTemp w limb 0)) (bdTemp w limb 2) ∧
    chunkXor 8 (bdLowD w limb) (bdTemp w limb 1 - 256 * bdTemp w limb 3) (bdTemp w limb 4) ∧
    chunkXor 8 (bdHighD w limb) (2 * bdTemp w limb 2 + bdTemp w limb 3) (bdTemp w limb 5) := by
  have hp : FieldCapacity.AtLeast p 512 := by
    rw [serialized_field compatible]
    decide
  rcases NativeFinalBDBindings.columns compatible w limb with
    ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22, a30, a31, a32⟩
  have q0 := final_query hp (bdIndex limb) 0 2 h (NativeFinalQueryShapes.bd_tag w limb 0)
  have q1 := final_query hp (bdIndex limb) 1 1 h (NativeFinalQueryShapes.bd_tag w limb 1)
  have q2 := final_query hp (bdIndex limb) 2 0 h (NativeFinalQueryShapes.bd_tag w limb 2)
  have q3 := final_query hp (bdIndex limb) 3 0 h (NativeFinalQueryShapes.bd_tag w limb 3)
  exact ⟨by simpa [a00, a01, a02] using q0,
    by simpa [a10, a11, a12] using q1,
    by simpa [a20, a21, a22] using q2,
    by simpa [a30, a31, a32] using q3⟩

end Airbender.Blake2Round.Proofs
