module
public import Slop.UnifiedReduced
public import Slop.Lookups

@[expose] public section

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem word_memory_address [Fact p.Prime] (hp : 196608 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} (store : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 28 = if store then 0 else 1) (other : w 29 = if store then 1 else 0)
    (sourceBound : (Word.mk (w 36).val (w 37).val).Bounded)
    (immediateBound : (Word.mk (w 8).val (w 9).val).Bounded)
    (addressBound : (Word.mk (w (if store then 44 else 38)).val
      (w (if store then 45 else 39)).val).Bounded) :
    (Word.mk (w (if store then 44 else 38)).val (w (if store then 45 else 39)).val).toBitVec =
      (Word.mk (w 36).val (w 37).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec := by
  have low := Verification.assertion_of_holds holds ⟨30, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨31, by rw [constraint_count]; decide⟩
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
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true] at result ⊢
  all_goals apply (by simpa [Word.toBitVec, Word.value] using result : _ → _ → _)
  all_goals first | linear_combination low | linear_combination high

theorem word_memory_copy [Fact p.Prime] {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p} (store : Bool)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 28 = if store then 0 else 1) (other : w 29 = if store then 1 else 0)
    (ram : w 54 = 0) : w 50 = w 42 ∧ w 51 = w 43 := by
  have gate := Verification.assertion_of_holds holds ⟨39, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds holds ⟨40, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨41, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, ram] at gate
  have disabled : w 81 = 0 := gate
  cases store
  all_goals simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected, other, disabled] at low high
  all_goals constructor
  all_goals first | linear_combination low | linear_combination high

end Airbender.UnifiedReduced.Proofs
