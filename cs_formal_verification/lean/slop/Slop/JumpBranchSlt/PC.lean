module
public import Mathlib.Tactic.LinearCombination
public import Human.Helpers.Properties
public import Slop.Arithmetic.Lemmas
public import Slop.Constraints
public import Slop.JumpBranchSlt.ArtifactChecks
public import Slop.JumpBranchSlt.OpIndex

@[expose] public section

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic

/-- Shared Boolean carry extraction for comparisons, branches and jumps. -/
theorem pc_carries {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c b : Nat, c ≤ 1 ∧ b ≤ 1 ∧ w 39 = (c : ZMod p) ∧ w 40 = (b : ZMod p) := by
  have carry := Verification.assertion_of_holds h
    ⟨21, by rw [constraint_count]; decide⟩
  have wrap := Verification.assertion_of_holds h
    ⟨22, by rw [constraint_count]; decide⟩
  op_index at carry wrap
  simp [Expression.eval, Verification.environment] at carry wrap
  obtain ⟨c, cb, hc⟩ := boolean_nat (x := w 39)
    (by simpa [mul_eq_zero, sub_eq_add_neg] using carry)
  obtain ⟨b, bb, hb⟩ := boolean_nat (x := w 40)
    (by simpa [mul_eq_zero, sub_eq_add_neg] using wrap)
  exact ⟨c, b, cb, bb, hc, hb⟩

end Airbender.JumpBranchSlt.Proofs
