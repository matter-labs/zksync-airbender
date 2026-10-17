import Airbender.Review.Circuits.WordMemory.Model
import Airbender.Proofs.WordMemory.Tables

namespace Airbender.WordMemory.Proofs
open Verification

variable {p : Nat} [Fact p.Prime] {rom : WordROM} {w : Nat → ZMod p}

private theorem equations
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    w 12 * (w 12 - 1) = 0 ∧ w 12 * (1 - w 22) = 0 ∧
    w 24 = (1 - w 12) * (1 - w 22) ∧ w 25 = (1 - w 12) * w 22 ∧
    w 28 = (1 - w 12) * w 19 + w 12 * w 6 ∧ w 29 = (1 - w 12) * w 20 ∧
    w 32 = 1 - w 12 ∧
    w 33 = w 12 * w 19 + (1 - w 12) * w 7 ∧ w 34 = w 12 * w 20 ∧
    w 39 = w 24 * w 26 + w 25 * w 30 ∧
    w 40 = w 24 * w 27 + w 25 * w 31 ∧
    w 41 = (1 - w 8) * w 39 ∧ w 42 = (1 - w 8) * w 40 ∧
    (1 - w 12) * (w 41 - w 37) = 0 ∧ (1 - w 12) * (w 42 - w 38) = 0 ∧
    w 12 * (w 30 - w 37) = 0 ∧ w 12 * (w 31 - w 38) = 0 := by
  repeat' apply And.intro
  · have equation := assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨10, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination equation
  · have equation := assertion_of_holds h ⟨11, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨12, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨13, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨14, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨32, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨15, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨16, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨17, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨18, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨19, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨20, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination -equation
  · have equation := assertion_of_holds h ⟨21, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination equation
  · have equation := assertion_of_holds h ⟨22, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination equation
  · have equation := assertion_of_holds h ⟨23, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination equation
  · have equation := assertion_of_holds h ⟨24, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment] at equation
    linear_combination equation

theorem transfers (hp : 4194304 < p)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) :
    NativeTransfers rom w := by
  obtain ⟨bit, noStore, romLoad, ramLoad, readLo, readHi, writeSpace,
    writeLo, writeHi, candidateLo, candidateHi, maskedLo, maskedHi,
    loadLo, loadHi, storeLo, storeHi⟩ := equations h
  have separator := (separator_values (by omega) h).1
  obtain ⟨alignment, romLo, romHi⟩ := rom_values hp h
  refine ⟨?_, address_bounds h, alignment, ⟨readLo, readHi⟩,
    ⟨writeSpace, writeLo, writeHi⟩, ?_, ?_⟩
  · rcases mul_eq_zero.mp bit with hz | ho
    · exact Or.inl hz
    · exact Or.inr (sub_eq_zero.mp ho)
  · intro load
    simp only [load, sub_zero, one_mul] at romLoad ramLoad loadLo loadHi
    have lo : w 37 = (1 - w 8) * ((1 - w 22) * w 26 + w 22 * w 30) := by
      rw [← romLoad, ← ramLoad, ← candidateLo, ← maskedLo]
      exact (sub_eq_zero.mp loadLo).symm
    have hi : w 38 = (1 - w 8) * ((1 - w 22) * w 27 + w 22 * w 31) := by
      rw [← romLoad, ← ramLoad, ← candidateHi, ← maskedHi]
      exact (sub_eq_zero.mp loadHi).symm
    dsimp
    rw [separator, romLo] at lo
    rw [separator, romHi] at hi
    split_ifs with region
    · simpa only [region, if_true, sub_zero, one_mul, zero_mul, add_zero] using And.intro lo hi
    · simpa only [region, if_false, sub_self, zero_mul, one_mul, zero_add] using And.intro lo hi
  · intro store
    simp only [store, one_mul] at noStore storeLo storeHi
    refine ⟨?_, (sub_eq_zero.mp storeLo).symm, (sub_eq_zero.mp storeHi).symm⟩
    by_contra region
    have regionBound : (w 20).val < 64 := by omega
    have isROM : w 22 = 0 := by simpa only [if_pos regionBound] using separator
    rw [isROM] at noStore
    simp at noStore

end Airbender.WordMemory.Proofs
