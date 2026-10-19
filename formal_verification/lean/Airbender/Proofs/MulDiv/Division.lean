import Airbender.Proofs.MulDiv.Product

namespace Airbender.MulDiv.Proofs
open Arithmetic Verification

variable {w : Nat → ZMod mersenne31Modulus}

/-- The inverse equations determine the divisor-zero flag without a supplied
    zero-test table or desired quotient premise. -/
theorem divisor_flag
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    w 52 = if (right w).value = 0 then 1 else 0 := by
  have e0 := assertion_of_holds holds ⟨28,by rw [constraint_count]; decide⟩
  have e1 := assertion_of_holds holds ⟨29,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e0 e1
  by_cases zero : (right w).value = 0
  · rw [if_pos zero]
    have low : (w 21).val = 0 := by dsimp [right,Word.value,limbBase] at zero; omega
    have high : (w 22).val = 0 := by dsimp [right,Word.value,limbBase] at zero; omega
    have lo : w 21 = 0 := by rw [← ZMod.natCast_zmod_val (w 21),low]; rfl
    have hi : w 22 = 0 := by rw [← ZMod.natCast_zmod_val (w 22),high]; rfl
    simp [lo,hi] at e0
    linear_combination e0
  · rw [if_neg zero]
    have bounds := (byte_words holds).2.1
    have size : 131072 < mersenne31Modulus := by decide
    have sum : w 21 + w 22 ≠ 0 := by
      intro same
      have natural : (w 21).val + (w 22).val = 0 :=
        bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
          (by dsimp [right,Word.Bounded,limbBase] at bounds; omega) (by omega)
          (by simpa only [Nat.cast_add,Nat.cast_zero,ZMod.natCast_zmod_val] using same)
      apply zero
      dsimp [right,Word.value,limbBase]
      omega
    have product : w 52 * (w 21 + w 22) = 0 := by linear_combination e1
    exact (mul_eq_zero.mp product).resolve_right sum

/-- The native comparison's low borrow uses 32768, the inverse of 65536 in
    Mersenne31. Its forced high borrow bounds every nonzero division remainder. -/
theorem remainder_lt_divisor
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (division : w 17 = 1) (nonzero : (right w).value ≠ 0) :
    (rawHigh w).value < (right w).value := by
  have zeroFlag := divisor_flag holds
  rw [if_neg nonzero] at zeroFlag
  have e0 := assertion_of_holds holds ⟨30,by rw [constraint_count]; decide⟩
  have e1 := assertion_of_holds holds ⟨33,by rw [constraint_count]; decide⟩
  have e2 := assertion_of_holds holds ⟨34,by rw [constraint_count]; decide⟩
  have e3 := assertion_of_holds holds ⟨46,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e0 e1 e2 e3
  have dzero : w 54 = 0 := by rw [division,zeroFlag] at e0; linear_combination -e0
  have borrow : w 57 = 1 := by rw [division,dzero] at e2; linear_combination -e2
  let b : ZMod mersenne31Modulus := 32768 * (w 55 + w 21 - w 25)
  have boolean : b * (b - 1) = 0 := by
    dsimp [b]
    have modulusZero : (2147483647 : ZMod mersenne31Modulus) = 0 := by decide
    linear_combination (norm := (ring_nf; simp [modulusZero])) e1
  obtain ⟨c,small,same⟩ := boolean_nat boolean
  have inverse : (32768 : ZMod mersenne31Modulus) * 65536 = 1 := by decide
  have low : w 55 + w 21 = w 25 + 65536 * (c : ZMod mersenne31Modulus) := by
    have scale := congrArg (fun x : ZMod mersenne31Modulus => 65536 * x) same
    have identity : 65536 * b = w 55 + w 21 - w 25 := by
      dsimp [b]
      calc
        _ = (32768 * 65536 : ZMod mersenne31Modulus) * (w 55 + w 21 - w 25) := by ring
        _ = _ := by rw [inverse]; ring
    rw [identity] at scale
    linear_combination scale
  have high : (c : ZMod mersenne31Modulus) + w 56 + w 22 = w 26 + 65536 := by
    rw [borrow] at e3
    dsimp [b] at same
    linear_combination -e3 - same
  have ranges := local_ranges holds
  apply Word.lt_of_borrow (p := mersenne31Modulus) (by decide)
    (output := rawHigh w) (modulus := right w)
    (remainder := ⟨(w 55).val,(w 56).val⟩)
    ⟨ranges 25 (by simp),ranges 26 (by simp)⟩ (byte_words holds).2.1
    ⟨ranges 55 (by simp),ranges 56 (by simp)⟩ small
  · simpa [rawHigh,right,ZMod.natCast_zmod_val] using low
  · simpa [rawHigh,right,ZMod.natCast_zmod_val] using high

/-- Nonzero quotient and remainder follow from exact product decomposition
    and strict comparison, through the shared natural division uniqueness rule. -/
theorem division_nonzero
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (division : w 17 = 1) (leftBound : (left w).Bounded)
    (nonzero : (right w).value ≠ 0) :
    (rawLow w).value = (left w).value / (right w).value ∧
    (rawHigh w).value = (left w).value % (right w).value := by
  have product := product_with_remainder holds leftBound
  have roles := word_wiring holds true division
  rw [roles.1,roles.2.1,roles.2.2.1,roles.2.2.2] at product
  change (rawLow w).value * (right w).value + (rawHigh w).value = (left w).value + wordModulus * 0 at product
  rw [mul_zero,add_zero] at product
  have unique := (Nat.div_mod_unique (a := (left w).value)
    (d := (rawLow w).value) (c := (rawHigh w).value)
    (Nat.pos_of_ne_zero nonzero)).mpr
    ⟨by simpa [mul_comm,add_comm] using product,remainder_lt_divisor holds division nonzero⟩
  exact ⟨unique.1.symm,unique.2.symm⟩

/-- Native division-by-zero equations force an all-ones quotient; the exact
    product relation forces the remainder to equal the dividend. -/
theorem division_zero
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (division : w 17 = 1) (leftBound : (left w).Bounded)
    (zero : (right w).value = 0) :
    (rawLow w).value = wordModulus - 1 ∧ (rawHigh w).value = (left w).value := by
  have zeroFlag := divisor_flag holds
  rw [if_pos zero] at zeroFlag
  have e0 := assertion_of_holds holds ⟨30,by rw [constraint_count]; decide⟩
  have e1 := assertion_of_holds holds ⟨31,by rw [constraint_count]; decide⟩
  have e2 := assertion_of_holds holds ⟨32,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e0 e1 e2
  have dzero : w 54 = 1 := by rw [division,zeroFlag] at e0; linear_combination -e0
  have lo : w 23 = 65535 := by rw [dzero] at e1; linear_combination e1
  have hi : w 24 = 65535 := by rw [dzero] at e2; linear_combination e2
  constructor
  · simp only [rawLow,Word.value,lo,hi]
    rw [show (65535 : ZMod mersenne31Modulus).val = 65535 from by decide]
    rfl
  · have product := product_with_remainder holds leftBound
    have roles := word_wiring holds true division
    rw [roles.1,roles.2.1,roles.2.2.1,roles.2.2.2,zero] at product
    simpa [Word.value] using product

end Airbender.MulDiv.Proofs
