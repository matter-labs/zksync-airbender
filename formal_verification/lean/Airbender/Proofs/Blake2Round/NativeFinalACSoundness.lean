import Airbender.Proofs.Blake2Round.NativeFinalACBindings
import Airbender.Proofs.Blake2Round.NativeFinalQueryBase

namespace Airbender.Blake2Round.Proofs
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem native_ac_queries_cached {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    (limb : Fin 8) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w limb 0) (acLowC w limb) (acTemp w limb 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w limb - acTemp w limb 0))
      ((-15728640 : ZMod p) * (acC w limb - acLowC w limb)) (acTemp w limb 2) ∧
    chunkXor 7 (acTemp w limb 1) (acLowA w limb) (acTemp w limb 4) ∧
    chunkXor 9 (acTemp w limb 2)
      ((-15728640 : ZMod p) * (acA w limb - acLowA w limb)) (acTemp w limb 5) := by
  have hp : FieldCapacity.AtLeast p 512 := by
    rw [serialized_field compatible]
    decide
  rcases NativeFinalACBindings.columns compatible w limb with
    ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22, a30, a31, a32⟩
  have q0 := final_query hp (limb.castLE (by decide)) 0 1 h (NativeFinalQueryShapes.ac_tag w limb 0)
  have q1 := final_query hp (limb.castLE (by decide)) 1 2 h (NativeFinalQueryShapes.ac_tag w limb 1)
  have q2 := final_query hp (limb.castLE (by decide)) 2 1 h (NativeFinalQueryShapes.ac_tag w limb 2)
  have q3 := final_query hp (limb.castLE (by decide)) 3 2 h (NativeFinalQueryShapes.ac_tag w limb 3)
  exact ⟨by simpa [a00, a01, a02] using q0,
    by simpa [a10, a11, a12] using q1,
    by simpa [a20, a21, a22] using q2,
    by simpa [a30, a31, a32] using q3⟩

end Airbender.Blake2Round.Proofs
