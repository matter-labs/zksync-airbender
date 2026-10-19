import Airbender.Proofs.MulDiv.Division

namespace Airbender.MulDiv.Proofs
open Arithmetic Verification

variable {w : Nat → ZMod mersenne31Modulus}

/-- Unique low/high decomposition of the native multiplication product. -/
theorem multiplication_results
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (division : w 17 = 0) (leftBound : (left w).Bounded) :
    (rawLow w).value = (left w).value * (right w).value % wordModulus ∧
    (rawHigh w).value = (left w).value * (right w).value / wordModulus := by
  have product := product_with_remainder holds leftBound
  have roles := word_wiring holds false division
  rw [roles.1,roles.2.1,roles.2.2.1,roles.2.2.2] at product
  change (left w).value * (right w).value + 0 =
    (rawLow w).value + wordModulus * (rawHigh w).value at product
  rw [add_zero] at product
  have ranges := local_ranges holds
  have bounded : (rawLow w).Bounded := ⟨ranges 23 (by simp),ranges 24 (by simp)⟩
  have unique := (Nat.div_mod_unique
    (a := (left w).value * (right w).value) (b := wordModulus)
    (d := (rawHigh w).value) (c := (rawLow w).value) (by decide)).mpr
    ⟨by simpa [add_comm] using product.symm,Word.value_lt bounded⟩
  exact ⟨unique.2.symm,unique.1.symm⟩

theorem division_results
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (division : w 17 = 1) (leftBound : (left w).Bounded) :
    (rawLow w).value = (if (right w).value = 0 then wordModulus - 1
      else (left w).value / (right w).value) ∧
    (rawHigh w).value = (left w).value % (right w).value := by
  by_cases zero : (right w).value = 0
  · simpa [zero] using division_zero holds division leftBound zero
  · simpa [zero] using division_nonzero holds division leftBound zero

/-- Native low/high selection precedes the actual destination-zero mask. -/
theorem selected_raw
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (lowHalf : Bool) (flag : w 18 = if lowHalf then 1 else 0) :
    selectedWord w = if lowHalf then rawLow w else rawHigh w := by
  have e0 := assertion_of_holds holds ⟨26,by rw [constraint_count]; decide⟩
  have e1 := assertion_of_holds holds ⟨27,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e0 e1
  have lo : w 50 = if lowHalf then w 23 else w 25 := by
    cases lowHalf <;> simp only [Bool.false_eq_true,if_false,if_true] at flag ⊢ <;>
      rw [flag] at e0 <;> linear_combination -e0
  have hi : w 51 = if lowHalf then w 24 else w 26 := by
    cases lowHalf <;> simp only [Bool.false_eq_true,if_false,if_true] at flag ⊢ <;>
      rw [flag] at e1 <;> linear_combination -e1
  cases lowHalf <;> simp only [Bool.false_eq_true,if_false,if_true] at lo hi ⊢
  all_goals exact congrArg₂ Word.mk (congrArg ZMod.val lo) (congrArg ZMod.val hi)

/-- Accepted native writes discard the selected value precisely when the
    supplied decoder-interface flag says the destination is x0. -/
theorem written_mask
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (discarded : Bool) (zeroFlag : w 8 = if discarded then 1 else 0) :
    writtenWord w = if discarded then ⟨0,0⟩ else selectedWord w := by
  have e0 := assertion_of_holds holds ⟨35,by rw [constraint_count]; decide⟩
  have e1 := assertion_of_holds holds ⟨36,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at e0 e1
  have lo : w 60 = if discarded then 0 else w 50 := by
    cases discarded <;> simp only [Bool.false_eq_true,if_false,if_true] at zeroFlag ⊢ <;>
      rw [zeroFlag] at e0 <;> linear_combination -e0
  have hi : w 61 = if discarded then 0 else w 51 := by
    cases discarded <;> simp only [Bool.false_eq_true,if_false,if_true] at zeroFlag ⊢ <;>
      rw [zeroFlag] at e1 <;> linear_combination -e1
  cases discarded <;> simp only [Bool.false_eq_true,if_false,if_true] at lo hi ⊢
  all_goals
    apply congrArg₂ Word.mk
    · simpa using congrArg ZMod.val lo
    · simpa using congrArg ZMod.val hi

/-- Calculation assembly stays outside the public review surface. -/
theorem native_result
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (operation : Operation) (selected : (w 12).val = operation.nativeMask)
    (leftBound : (left w).Bounded) :
    (selectedWord w).value = operation.result (left w) (right w) := by
  have flags := selected_flags holds operation selected
  have output := selected_raw holds operation.lowHalf flags.2
  cases operation <;>
    simp only [Operation.division,Operation.lowHalf,Bool.false_eq_true,if_false,if_true] at flags output
  · rw [output]
    exact (multiplication_results holds flags.1 leftBound).1
  · rw [output]
    exact (multiplication_results holds flags.1 leftBound).2
  · rw [output]
    exact (division_results holds flags.1 leftBound).1
  · rw [output]
    exact (division_results holds flags.1 leftBound).2

theorem native_masked_result
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (operation : Operation) (discarded : Bool)
    (selected : (w 12).val = operation.nativeMask) (leftBound : (left w).Bounded)
    (zeroFlag : w 8 = if discarded then 1 else 0) :
    (selectedWord w).value = operation.result (left w) (right w) ∧
      (writtenWord w).value = if discarded then 0 else operation.result (left w) (right w) := by
  have result := native_result holds operation selected leftBound
  refine ⟨result,?_⟩
  rw [written_mask holds discarded zeroFlag]
  cases discarded
  · exact result
  · rfl

end Airbender.MulDiv.Proofs
