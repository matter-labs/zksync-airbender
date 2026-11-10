import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.Binary
import Airbender.Proofs.UnifiedReduced.XorRotateLookups

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem xorrot_query_values [Fact p.Prime] (hp : FieldCapacity.NoWrap p 256)
    {before : Reference.RiscV.Sail.State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table before)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (kind : Fin 4) (funct3 : w 10 = (47 + kind.val : Nat)) (i : Fin 4) :
    (leftByte w i).val < 256 ∧ (rightByte w i + immediateByte w i).val < 256 ∧
      ∀ byte : Fin 4, w (58 + 4 * i.val + byte.val) =
        (((BitVec.ofNat 32 ((leftByte w i).val ^^^ (rightByte w i + immediateByte w i).val)).rotateRight
          (#[16, 12, 8, 7][kind.val]!)).extractLsb' (8 * byte.val) 8).toNat := by
  have wires := binary_wiring holds selected other i
  have query := Verification.lookup_of_holds holds
    ⟨14 + i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  fin_cases i
  all_goals
    norm_num only at wires
    obtain ⟨found, same, left, right, outputs⟩ := Setup.Proofs.rotate_lookup hp query
      (47 + kind.val) (by omega) (by have := kind.isLt; omega)
      (by simpa [Expression.eval, Verification.environment] using wires.1.trans funct3)
    have identical : found = kind := by
      apply Fin.ext
      have := kind.isLt
      omega
    subst found
    have a := wires.2.1
    have b := wires.2.2.1
    refine ⟨?_, ?_, ?_⟩
    · simpa [Expression.eval, Verification.environment, a] using left
    · simpa [Expression.eval, Verification.environment, b] using right
    · intro byte
      have output := outputs byte
      have c := wires.2.2.2.1 byte
      fin_cases byte
      all_goals norm_num only at c output ⊢
      all_goals simpa [Expression.eval, Verification.environment, a, b, c] using output

end Airbender.UnifiedReduced.Proofs
