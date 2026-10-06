import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Review.Properties
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Constraints
import Mathlib.Tactic.FinCases

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic

/-- Local flag bounds, without assuming decoded instruction identity. -/
theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ k : Fin 5, w (11 + k.val) = 0 ∨ w (11 + k.val) = 1 := by
  constructor
  · have flag := Verification.assertion_of_holds h
      ⟨0, by simp [importedConstraints, FlatOperation.constraints]⟩
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] using flag
  · intro k
    have index : 14 + k.val < (FlatOperation.constraints (importedConstraints (p := p))).length := by
      rw [constraint_count]
      have := k.isLt
      omega
    have flag := Verification.assertion_of_holds h ⟨14 + k.val, index⟩
    fin_cases k <;>
      simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] using flag

/-- Canonical bounds from all four imported range queries. PC alignment and
    full final-PC interpretation still need generic lookup semantics. -/
theorem local_ranges {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 34).val < limbBase ∧ (w 35).val < limbBase ∧
      (w 1).val < limbBase ∧ (w 36).val < limbBase := by
  have a := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨0, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have b := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨1, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have c := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨2, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have d := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at a b c d
  exact ⟨a, b, c, d⟩

/-- Reuse the same four-tick carry algebra as ADD/SUB, with this artifact's roles. -/
theorem timestamp_equations {p : Nat} [Fact p.Prime]
    (inverse : (-3840 : ZMod p) * 524288 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 18 + 524288 * c ∧ w 3 + c = w 19 := by
  have carry := Verification.assertion_of_holds h
    ⟨12, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨13, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at carry high
  have boolean : (-3840 * (w 2 + 4 - w 18)) *
      (-3840 * (w 2 + 4 - w 18) - 1) = 0 := by
    convert carry using 1
    ring
  have normalized : -3840 * (w 2 + 4 - w 18) + w 3 - w 19 = 0 := by
    linear_combination -high
  exact Arithmetic.increment_carry inverse boolean normalized

/-- The comparison branch computes the unsigned borrow. The generic resolution
    lookup still connects this borrow to the signed/unsigned destination choice. -/
theorem unsigned_borrow {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (immediate : w 8 = 0 ∧ w 9 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 = (right.lo : ZMod p) ∧ w 27 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 38 = 1 ↔ left.value < right.value := by
  have carry := Verification.assertion_of_holds h
    ⟨19, by simp [importedConstraints, FlatOperation.constraints]⟩
  have borrow := Verification.assertion_of_holds h
    ⟨20, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at carry borrow
  obtain ⟨c, cb, hc⟩ := boolean_nat (x := w 37) (by simpa [mul_eq_zero, sub_eq_add_neg] using carry)
  obtain ⟨b, bb, hb⟩ := boolean_nat (x := w 38) (by simpa [mul_eq_zero, sub_eq_add_neg] using borrow)
  have low := Verification.assertion_of_holds h
    ⟨1, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨2, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected, other.1, other.2.1, other.2.2,
    immediate.1, immediate.2, mapping.1, mapping.2.1, mapping.2.2.1, mapping.2.2.2,
    hc, hb] at low high
  have bits : w 38 = 1 ↔ b = 1 := by
    rw [hb]
    have cases : b = 0 ∨ b = 1 := by omega
    rcases cases with rfl | rfl <;> simp
  rw [bits]
  have bounds := local_ranges h
  apply Word.borrow_iff hp leftBound rightBound (remainder := ⟨(w 34).val, (w 35).val⟩)
    ⟨bounds.1, bounds.2.1⟩ cb bb
  · simp only [ZMod.natCast_zmod_val]
    linear_combination low
  · simp only [ZMod.natCast_zmod_val]
    linear_combination high

end Airbender.JumpBranchSlt.Proofs
