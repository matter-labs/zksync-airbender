module
public import Slop.AddSub.ArtifactChecks
public import Slop.AddSub.OpIndex
public import Human.Helpers.Properties
public import Slop.Constraints
public import Mathlib.Tactic.FinCases
public import Slop.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.AddSub.Proofs

/-- Booleanity is enforced locally; instruction identity and exclusivity still
    require the decoder interface. -/
theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ k : Fin 9, w (10 + k.val) = 0 ∨ w (10 + k.val) = 1 := by
  constructor
  · have flag := Verification.assertion_of_holds h
      ⟨0, by rw [constraint_count]; decide⟩
    op_index at flag
    simpa [Expression.eval, Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] using flag
  · intro k
    have index : 16 + k.val < (FlatOperation.constraints (importedConstraints (p := p))).length := by
      rw [constraint_count]
      have := k.isLt
      omega
    have flag := Verification.assertion_of_holds h ⟨16 + k.val, index⟩
    fin_cases k <;> op_index at flag <;>
      simpa [Expression.eval, Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] using flag

/-- Delegation enforces zero source value, timeless source access and discarded
    destination limbs. Dispatch identity and delegated effects belong to external interfaces. -/
theorem delegation_zeroes {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 17 = 1) :
    w 29 = 0 ∧ w 30 = 0 ∧ w 27 = 0 ∧ w 28 = 0 ∧ w 33 = 0 ∧ w 34 = 0 := by
  have sourceLo := Verification.assertion_of_holds h ⟨6, by rw [constraint_count]; decide⟩
  have sourceHi := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  have timeLo := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  have timeHi := Verification.assertion_of_holds h ⟨9, by rw [constraint_count]; decide⟩
  have destLo := Verification.assertion_of_holds h ⟨10, by rw [constraint_count]; decide⟩
  have destHi := Verification.assertion_of_holds h ⟨11, by rw [constraint_count]; decide⟩
  op_index at sourceLo sourceHi timeLo timeHi destLo destHi
  simp [Expression.eval, Verification.environment, selected] at sourceLo sourceHi timeLo timeHi destLo destHi
  exact ⟨sourceLo, sourceHi, timeLo, timeHi, destLo, destHi⟩

end Airbender.AddSub.Proofs
