import Airbender.Proofs.WordMemory.Tables
import Airbender.Review.Circuits.WordMemory.Model
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Mersenne31

namespace Airbender.WordMemory.Proofs
open Arithmetic Verification

/-- V2 encodes the low carry in Mersenne31 as 32768 times the limb difference.
    The native characteristic and inverse are checked, without source-field premises. -/
theorem effective_address {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (sourceBound : (sourceWord w).Bounded) (immediateBound : (immediateWord w).Bounded) :
    (addressWord w).toBitVec = (sourceWord w).toBitVec + (immediateWord w).toBitVec := by
  have bit := assertion_of_holds h ⟨9, by rw [constraint_count]; decide⟩
  have wrap := assertion_of_holds h ⟨0, by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨31, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at bit wrap high
  let carry : ZMod mersenne31Modulus := 32768 * (w 17 + w 9 - w 19)
  have carryBit : carry = 0 ∨ carry = 1 := by
    apply (mul_eq_zero.mp (show carry * (carry - 1) = 0 from ?_)).imp id (fun h => sub_eq_zero.mp h)
    dsimp [carry]
    linear_combination (norm := ring_nf) bit
    simp [show (2147483647 : ZMod mersenne31Modulus) = 0 from by decide]
  have wrapBit : w 21 = 0 ∨ w 21 = 1 := by
    have polynomial : w 21 * (w 21 - 1) = 0 := by convert wrap using 1; ring
    exact (mul_eq_zero.mp polynomial).imp id (fun h => sub_eq_zero.mp h)
  have inverse : (65536 : ZMod mersenne31Modulus) * 32768 = 1 := by decide
  have low : w 17 + w 9 = w 19 + 65536 * carry := by
    dsimp [carry]
    linear_combination -(w 17 + w 9 - w 19) * inverse
  have upper : carry + w 18 + w 10 = w 20 + 65536 * w 21 := by
    dsimp [carry]
    linear_combination high
  have bounds : (addressWord w).Bounded := address_bounds h
  have result := Word.add_of_limbs (p := mersenne31Modulus) (by decide) sourceBound
    (right := ⟨0, 0⟩) (by exact ⟨by decide, by decide⟩) immediateBound bounds
    (Nat.le_trans (boolean_val carryBit) (by decide))
    (Nat.le_trans (boolean_val wrapBit) (by decide))
    (by simpa [sourceWord, immediateWord, addressWord] using low)
    (by simpa [sourceWord, immediateWord, addressWord] using upper)
  simpa [Word.toBitVec, Word.value] using result

end Airbender.WordMemory.Proofs
