import Airbender.Review.AddSub.Artifact
import Airbender.Review.Properties
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.Constraints

namespace Airbender.AddSub.Proofs

/-- The retained timestamp assertions enforce a four-tick increment in radix 2^19.
    These field equations hold independently of execute/selectors. Integer bounds
    and global timestamp ordering require the timestamp lookup/state interfaces. -/
theorem timestamp_equations {p : Nat} [Fact p.Prime]
    (inverse : (-3840 : ZMod p) * 524288 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 21 + 524288 * c ∧ w 3 + c = w 22 := by
  have carry := Verification.assertion_of_holds h
    ⟨14, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨15, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at carry high
  have boolean : (-3840 * (w 2 + 4 - w 21)) *
      (-3840 * (w 2 + 4 - w 21) - 1) = 0 := by
    convert carry using 1
    ring
  have normalized : -3840 * (w 2 + 4 - w 21) + w 3 - w 22 = 0 := by
    linear_combination -high
  exact Arithmetic.increment_carry inverse boolean normalized

end Airbender.AddSub.Proofs
