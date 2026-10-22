import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced
import Airbender.Proofs.Lookups

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem word_memory_address [Fact p.Prime] (hp : FieldCapacity.NoWrap p 196608)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} (store : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 28 = if store then 0 else 1) (other : w 29 = if store then 1 else 0)
    (sourceBound : (Word.mk (w 36).val (w 37).val).Bounded)
    (immediateBound : (Word.mk (w 8).val (w 9).val).Bounded)
    (addressBound : (Word.mk (w (if store then 44 else 38)).val
      (w (if store then 45 else 39)).val).Bounded) :
    (Word.mk (w (if store then 44 else 38)).val (w (if store then 45 else 39)).val).toBitVec =
      (Word.mk (w 36).val (w 37).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec := by
  have low := Verification.assertion_of_holds holds ⟨33, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨34, by rw [constraint_count]; decide⟩
  have carry := boolean_val (local_flags holds 20)
  have wrap := boolean_val (local_flags holds 21)
  have zeroBound : (⟨0, 0⟩ : Word).Bounded := ⟨by decide, by decide⟩
  have result := Word.add_of_limbs (p := p) hp
    (left := Word.mk (w 36).val (w 37).val) (right := ⟨0, 0⟩)
    (immediate := Word.mk (w 8).val (w 9).val)
    (output := Word.mk (w (if store then 44 else 38)).val (w (if store then 45 else 39)).val)
    sourceBound zeroBound immediateBound addressBound (Nat.le_trans carry (by decide))
    (Nat.le_trans wrap (by decide))
  cases store
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected, other] at low high
  all_goals simp only [Bool.false_eq_true, if_false, if_true] at result ⊢
  all_goals apply (by simpa [Word.toBitVec, Word.value] using result : _ → _ → _)
  all_goals first | linear_combination low | linear_combination high

theorem word_memory_copy [Fact p.Prime] {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p} (store : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 28 = if store then 0 else 1) (other : w 29 = if store then 1 else 0)
    (ram : w 54 = 0) : w 50 = w 42 ∧ w 51 = w 43 := by
  have gate := Verification.assertion_of_holds holds ⟨42, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds holds ⟨43, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨44, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, ram] at gate
  have disabled : w 87 = 0 := gate
  cases store
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected, other, disabled] at low high
  all_goals constructor
  all_goals first | linear_combination low | linear_combination high

theorem word_memory_ram [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} (store : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 28 = if store then 0 else 1) (other : w 29 = if store then 1 else 0)
    (addressHi : 64 ≤ (w (if store then 45 else 39)).val) : w 54 = 0 := by
  have index := Verification.assertion_of_holds holds ⟨if store then 38 else 37, by rw [constraint_count]; split <;> decide⟩
  have residue := Verification.assertion_of_holds holds ⟨39, by rw [constraint_count]; decide⟩
  have range := Verification.range16_bound (Verification.lookup_of_holds holds ⟨10, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at range
  have indexed : w 58 = w (if store then 45 else 39) := by
    cases store
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected, other] at index
    all_goals simp only [Bool.false_eq_true, if_false, if_true]
    all_goals linear_combination index
  have upper : (w (if store then 45 else 39)).val < limbBase := by
    cases store
    · have bound := Verification.range16_bound (Verification.lookup_of_holds holds ⟨7, by rw [lookup_count]; decide⟩)
      simpa [Expression.eval, Verification.environment] using bound
    · have bound := Verification.range16_bound (Verification.lookup_of_holds holds ⟨9, by rw [lookup_count]; decide⟩)
      simpa [Expression.eval, Verification.environment] using bound
  have equation : w 86 + 64 = w 58 + 65536 * w 54 := by
    cases store
    all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected, other] at residue
    all_goals linear_combination residue
  have flag := local_flags holds 22
  change w 54 = 0 ∨ w 54 = 1 at flag
  rcases flag with zero | one
  · exact zero
  · rw [one, indexed] at equation
    have equal : (w 86).val + 64 = (w (if store then 45 else 39)).val + 65536 := by
      apply bounded_nat_eq (F := ZMod p) (p := p)
      · unfold limbBase at range; omega
      · unfold limbBase at upper; omega
      · simp only [mul_one] at equation
        simpa only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val] using equation
    unfold limbBase at range
    omega

end Airbender.UnifiedReduced.Proofs
