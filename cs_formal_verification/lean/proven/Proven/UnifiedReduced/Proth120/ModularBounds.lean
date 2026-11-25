module
public import Human.Circuits.UnifiedReduced.Proth120Modular
public import Proven.UnifiedReduced.Proth120.ArtifactChecks
public import Proven.Constraints
public import Proven.UnifiedReduced.Modular.Soundness
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Arithmetic

variable {setup : Table (ZMod proth120Modulus) (fields 10)} {w : Nat → ZMod proth120Modulus}

/-- The six leading range queries cover the comparison remainder, output and low quotient word. -/
theorem modular_ranges (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)) :
    (wordAt w 74).Bounded ∧ (wordAt w 50).Bounded ∧ (wordAt w 57).Bounded := by
  have ranged (i : Fin 6) : (w (#v[74,75,50,51,57,58][i])).val < limbBase := by
    have lookup := Verification.lookup_of_holds holds ⟨i.val, by rw [lookup_count]; omega⟩
    fin_cases i <;> op_index at lookup <;> simpa [Expression.eval, Verification.environment] using Verification.range16_bound lookup
  exact ⟨⟨ranged 0, ranged 1⟩, ⟨ranged 2, ranged 3⟩, ranged 4, ranged 5⟩

/-- The subtraction borrow and the quotient's three high bits are native Boolean assertions. -/
theorem modular_bits (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)) (i : Fin 4) :
    (w (53 + i.val)).val ≤ 1 := by
  have bit := Verification.assertion_of_holds holds ⟨111 + i.val, by rw [constraint_count]; omega⟩
  apply boolean_val
  fin_cases i <;> op_index at bit <;>
    simpa [Expression.eval, Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] using bit

theorem modular_canonical (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)) (s11 : w 11 = 0) (s12 : w 12 = 0) (s13 : w 13 = 0)
    (s20 : w 20 = 0) (selected : w 14 + w 15 + w 16 + w 17 = 1) :
    (wordAt w 50).value < babyBearModulus := by
  have borrow := Verification.assertion_of_holds holds ⟨3, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds holds ⟨4, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds holds ⟨5, by rw [constraint_count]; decide⟩
  op_index at borrow low high
  simp [Expression.eval, Verification.environment, s11, s12, s13, s20, selected] at borrow low high
  have one : w 52 = 1 := by linear_combination -borrow
  obtain ⟨remainder, output, _⟩ := modular_ranges holds
  apply Modular.canonical_of_comparison output remainder (modular_bits holds 0)
  · linear_combination low
  · rw [one] at high
    linear_combination high


end Airbender.UnifiedReduced.Proth120
