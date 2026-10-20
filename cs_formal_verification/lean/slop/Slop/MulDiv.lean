import Slop.MulDiv.ArtifactChecks
import Human.Helpers.Properties
import Slop.Arithmetic.Word
import Slop.Constraints
import Slop.Lookups
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace Airbender.MulDiv.Proofs
open Airbender.Arithmetic

theorem local_flags {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 4 = 0 ∨ w 4 = 1) ∧ ∀ i : Fin 4, w (10 + i.val) = 0 ∨ w (10 + i.val) = 1 := by
  constructor
  · have flag := Verification.assertion_of_holds h ⟨0, by rw [constraint_count]; decide⟩
    simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] using flag
  · intro i
    have flag := Verification.assertion_of_holds h
      ⟨36 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
    fin_cases i <;>
      simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] using flag

/-- Output, extra, comparison and final-PC limbs are bounded by the eight
    imported 16-bit queries, in that order. -/
theorem local_ranges {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∀ i : Fin 8, (w ([28, 29, 37, 38, 39, 40, 14, 15].get i)).val < limbBase := by
  intro i
  have query := Verification.lookup_of_holds h
    ⟨i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  fin_cases i <;> simpa [Expression.eval, Verification.environment] using
    (Verification.range16_bound query)

/-- Four real low-byte queries: the divisor and selected quotient limbs.
    The latter are resolved through checked scratch aliases during import. -/
theorem byte_values {p : Nat} [Fact p.Prime] (hp : 65536 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∀ i : Fin 4, let pair := [(24, 33), (25, 34), (49, 60), (50, 61)].get i
      (w pair.1).val < limbBase ∧ w pair.2 = (((w pair.1).val % 256 : Nat) : ZMod p) := by
  intro i
  let index := [9, 10, 14, 15].get i
  have query := Verification.lookup_of_holds h
    ⟨index, by dsimp [index]; fin_cases i <;> rw [lookup_count] <;> decide⟩
  fin_cases i <;> simpa [Expression.eval, Verification.environment, limbBase] using
    (Verification.u16LowByte_value hp query)

theorem carry_bounds {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∀ i : Fin 3, (w (41 + i.val)).val < 8192 := by
  intro i
  have query := Verification.lookup_of_holds h
    ⟨11 + i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  fin_cases i <;> simpa [Expression.eval, Verification.environment] using
    (Verification.range13_bound query)

/-- The zero flag is derived from fixed-table membership, not an interface. -/
theorem divisor_zero_iff {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    w 32 = 1 ↔ (⟨(w 24).val, (w 25).val⟩ : Word).value = 0 := by
  have bytes := byte_values (by omega) h
  have lo := (bytes ⟨0, by decide⟩).1
  have hi := (bytes ⟨1, by decide⟩).1
  dsimp at lo hi
  have zero := Verification.regIsZero_value hp (Verification.lookup_of_holds h
    ⟨8, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment, -ZMod.val_eq_zero] at zero
  have key : (w 24 + w 25).val = (w 24).val + (w 25).val := by
    have cast : w 24 + w 25 = (((w 24).val + (w 25).val : Nat) : ZMod p) := by simp
    rw [cast, ZMod.val_natCast, Nat.mod_eq_of_lt (by unfold limbBase at lo hi; omega)]
  rw [zero.2, key]
  have value : (⟨(w 24).val, (w 25).val⟩ : Word).value = 0 ↔
      (w 24).val + (w 25).val = 0 := by
    simp [Word.value, limbBase]
  rw [value]
  by_cases z : (w 24).val + (w 25).val = 0 <;> simp [z]

/-- Imported exceptional-case equations force DIVU=max and REMU=dividend.
    This is local arithmetic, not yet native Sail instruction soundness. -/
theorem division_by_zero {p : Nat} [Fact p.Prime] (hp : 131072 ≤ p)
    {w : Nat → ZMod p} (remainder : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 12 = (if remainder then 0 else 1) ∧ w 13 = (if remainder then 1 else 0))
    (other : w 10 = 0 ∧ w 11 = 0) (zero : w 24 = 0 ∧ w 25 = 0) :
    (⟨(w 28).val, (w 29).val⟩ : Word).toBitVec =
      (if remainder then (⟨(w 20).val, (w 21).val⟩ : Word).toBitVec else 0xffffffff) := by
  have isZero : w 32 = 1 := (divisor_zero_iff hp h).mpr (by simp [zero, Word.value])
  have flag := Verification.assertion_of_holds h ⟨1, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨2, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨3, by rw [constraint_count]; decide⟩
  have qlo := Verification.assertion_of_holds h ⟨6, by rw [constraint_count]; decide⟩
  have qhi := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  have rlo := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  have rhi := Verification.assertion_of_holds h ⟨9, by rw [constraint_count]; decide⟩
  have equalLo := Verification.assertion_of_holds h ⟨28, by rw [constraint_count]; decide⟩
  have equalHi := Verification.assertion_of_holds h ⟨29, by rw [constraint_count]; decide⟩
  have maxLo := Verification.assertion_of_holds h ⟨30, by rw [constraint_count]; decide⟩
  have maxHi := Verification.assertion_of_holds h ⟨31, by rw [constraint_count]; decide⟩
  cases remainder <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected.1, selected.2, other.1, other.2, isZero] at flag low high qlo qhi rlo rhi equalLo equalHi maxLo maxHi
  all_goals
    have flagEq : w 44 = 1 := by linear_combination flag
    simp [flagEq] at equalLo equalHi maxLo maxHi
  · have destLo : w 28 = 65535 := by linear_combination -maxLo - qlo
    have destHi : w 29 = 65535 := by linear_combination -maxHi - qhi
    have value : (65535 : ZMod p).val = 65535 := by
      change ((65535 : Nat) : ZMod p).val = _
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp [destLo, destHi, value, Word.toBitVec, Word.value, limbBase]
  · have destLo : w 28 = w 20 := by linear_combination -equalLo + low - rlo
    have destHi : w 29 = w 21 := by linear_combination -equalHi + high - rhi
    simp [destLo, destHi]

/-- The same serialized carry inverse and shared word-increment proof as ADD/SUB.
    This local PC update excludes 32-bit overflow. -/
theorem pc_successor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 14).val ∧ final.hi = (w 15).val)
    (initialBound : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 := by
  have carry := Verification.assertion_of_holds h ⟨32, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨33, by rw [constraint_count]; decide⟩
  have finalLo : w 14 = (final.lo : ZMod p) := by
    rw [mapping.2.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have finalHi : w 15 = (final.hi : ZMod p) := by
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
  have finalBounds : final.Bounded :=
    ⟨mapping.2.2.1 ▸ ranges ⟨6, by decide⟩, mapping.2.2.2 ▸ ranges ⟨7, by decide⟩⟩
  exact Word.increment_of_limbs (by omega) (by decide) cb initialBound finalBounds low hi

end Airbender.MulDiv.Proofs
