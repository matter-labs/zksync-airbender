import Slop.AddSub.ArtifactChecks
import Human.Helpers.Properties
import Slop.Constraints
import Mathlib.Tactic.FinCases

namespace Airbender.AddSub.Proofs

/-- Booleanity is enforced locally; instruction identity and exclusivity still
    require the decoder interface. -/
theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ k : Fin 9, w (10 + k.val) = 0 ∨ w (10 + k.val) = 1 := by
  constructor
  · have flag := Verification.assertion_of_holds h
      ⟨0, by simp [importedConstraints, FlatOperation.constraints]⟩
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] using flag
  · intro k
    have index : 16 + k.val < (FlatOperation.constraints (importedConstraints (p := p))).length := by
      rw [constraint_count]
      have := k.isLt
      omega
    have flag := Verification.assertion_of_holds h ⟨16 + k.val, index⟩
    fin_cases k <;>
      simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] using flag

/-- Delegation enforces zero source value, timeless source access and discarded
    destination limbs. Dispatch identity and delegated effects belong to external interfaces. -/
theorem delegation_zeroes {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 17 = 1) :
    w 29 = 0 ∧ w 30 = 0 ∧ w 27 = 0 ∧ w 28 = 0 ∧ w 33 = 0 ∧ w 34 = 0 := by
  have sourceLo := Verification.assertion_of_holds h ⟨6, by simp [importedConstraints, FlatOperation.constraints]⟩
  have sourceHi := Verification.assertion_of_holds h ⟨7, by simp [importedConstraints, FlatOperation.constraints]⟩
  have timeLo := Verification.assertion_of_holds h ⟨8, by simp [importedConstraints, FlatOperation.constraints]⟩
  have timeHi := Verification.assertion_of_holds h ⟨9, by simp [importedConstraints, FlatOperation.constraints]⟩
  have destLo := Verification.assertion_of_holds h ⟨10, by simp [importedConstraints, FlatOperation.constraints]⟩
  have destHi := Verification.assertion_of_holds h ⟨11, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected] at sourceLo sourceHi timeLo timeHi destLo destHi
  exact ⟨sourceLo, sourceHi, timeLo, timeHi, destLo, destHi⟩

end Airbender.AddSub.Proofs
