import Slop.JumpBranchSlt
import Mathlib.Tactic.LinearCombination
import Human.Circuits.JumpBranchSlt.Model

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic

/-- Shared Boolean carry extraction for comparisons, branches and jumps. -/
theorem pc_carries {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c b : Nat, c ≤ 1 ∧ b ≤ 1 ∧ w 39 = (c : ZMod p) ∧ w 40 = (b : ZMod p) := by
  have carry := Verification.assertion_of_holds h
    ⟨21, by simp [importedConstraints, FlatOperation.constraints]⟩
  have wrap := Verification.assertion_of_holds h
    ⟨22, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at carry wrap
  obtain ⟨c, cb, hc⟩ := boolean_nat (x := w 39)
    (by simpa [mul_eq_zero, sub_eq_add_neg] using carry)
  obtain ⟨b, bb, hb⟩ := boolean_nat (x := w 40)
    (by simpa [mul_eq_zero, sub_eq_add_neg] using wrap)
  exact ⟨c, b, cb, bb, hc, hb⟩

end Airbender.JumpBranchSlt.Proofs
