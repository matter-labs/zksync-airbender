import Airbender.Proofs.Blake2G.FragmentDefinitions
import Mathlib.Tactic.FinCases

namespace Airbender.Blake2G.Proofs

/-- Only the twelve arithmetic carries are needed by the reusable G proof. -/
theorem mixing_flags {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 9)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (mixingConstraints setup)) :
    ∀ i : Fin 12,
      w Variables.booleanColumns[1 + i.val] = 0 ∨ w Variables.booleanColumns[1 + i.val] = 1 := by
  intro i
  have flag := Verification.assertion_of_holds h
    ⟨8 + i.val, by rw [mixing_constraint_count]; have size := i.isLt; omega⟩
  fin_cases i <;> simp [mixingConstraints, importedConstraints, FlatOperation.constraints,
    Expression.eval, Verification.environment, Variables.booleanColumns,
    mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag ⊢
  all_goals exact flag

end Airbender.Blake2G.Proofs
