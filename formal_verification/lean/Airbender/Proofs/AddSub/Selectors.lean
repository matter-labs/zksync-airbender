import Airbender.Review.AddSub.Artifact
import Airbender.Review.Properties
import Airbender.Proofs.Constraints
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

end Airbender.AddSub.Proofs
