import Airbender.Review.ShiftBinop.Artifact
import Airbender.Review.Properties
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Constraints
import Mathlib.Tactic.FinCases

namespace Airbender.ShiftBinop.Proofs
open Airbender.Arithmetic

theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ i : Fin 2, w (11 + i.val) = 0 ∨ w (11 + i.val) = 1 := by
  constructor
  · have flag := Verification.assertion_of_holds h ⟨0, by rw [constraint_count]; decide⟩
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] using flag
  · intro i
    have flag := Verification.assertion_of_holds h
      ⟨47 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
    fin_cases i <;> simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] using flag

/-- Logical placement resolves both range queries to final-PC limbs. -/
theorem local_ranges {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 13).val < limbBase ∧ (w 14).val < limbBase := by
  have low := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨0, by rw [lookup_count]; decide⟩)
  have high := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨1, by rw [lookup_count]; decide⟩)
  simpa [Expression.eval, Verification.environment] using And.intro low high

/-- Shared two-limb increment. Final-PC bounds follow from the imported range
    queries; only initial bounds remain external. No 32-bit overflow. -/
theorem pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 13).val ∧ final.hi = (w 14).val)
    (initialBound : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 := by
  have carry := Verification.assertion_of_holds h ⟨43, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨44, by rw [constraint_count]; decide⟩
  have finalLo : w 13 = (final.lo : ZMod p) := by
    rw [mapping.2.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have finalHi : w 14 = (final.hi : ZMod p) := by
    rw [mapping.2.2.2]; exact (ZMod.natCast_zmod_val _).symm
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mapping.1, mapping.2.1, finalLo, finalHi] at carry high
  let x : ZMod p := -30720 * (initial.lo + 4 - final.lo)
  have boolean : x * (x - 1) = 0 := by
    simpa [x, mul_eq_zero, sub_eq_add_neg] using carry
  have normalized : x + initial.hi - final.hi = 0 := by
    convert high using 1
    dsimp [x]
    ring
  obtain ⟨c, cb, low, hi⟩ := increment_carry inverse boolean normalized
  have ranges := local_ranges h
  have finalBound : final.Bounded :=
    ⟨mapping.2.2.1 ▸ ranges.1, mapping.2.2.2 ▸ ranges.2⟩
  exact Word.increment_of_limbs (by omega) (by decide) cb initialBound finalBound low hi

end Airbender.ShiftBinop.Proofs
