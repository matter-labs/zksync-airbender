import Airbender.Review.Circuits.JumpBranchSlt.Artifact
import Airbender.Proofs.JumpBranchSlt.ArtifactChecks
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Constraints
import Airbender.Proofs.Lookups
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
    final-PC high-limb bounds still require a state/ROM interface. -/
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

/-- Values forced by the four imported fixed-table queries. -/
theorem lookup_values {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    w 41 = (if (w 34 + w 35).val = 0 then 1 else 0) ∧
    w 42 = (((w 23).val / 32768 : Nat) : ZMod p) ∧
    w 44 = (Verification.conditionalValue
      (w 43 + 65536 * w 42 + 131072 * w 38 + 262144 * w 41 + 524288 * w 10).val : ZMod p) ∧
    w 46 = (((w 36).val / 2 % 2 : Nat) : ZMod p) ∧
    w 16 = (((w 36).val - (w 36).val % 4 : Nat) : ZMod p) := by
  have zero := Verification.regIsZero_value (by omega : 131072 ≤ p)
    (Verification.lookup_of_holds h ⟨4, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have sign := Verification.u16Sign_value (by omega : 65536 ≤ p)
    (Verification.lookup_of_holds h ⟨5, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have resolved := Verification.conditional_value hp
    (Verification.lookup_of_holds h ⟨6, by simp [importedConstraints, FlatOperation.lookups]⟩)
  have cleanup := Verification.jumpCleanup_value (by omega : 65536 ≤ p)
    (Verification.lookup_of_holds h ⟨7, by simp [importedConstraints, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at zero sign resolved cleanup
  refine ⟨by simpa using zero.2, sign.2, ?_, cleanup.2.1, cleanup.2.2⟩
  simpa [add_assoc, add_comm, add_left_comm] using resolved.2

/-- Decode the packed resolution key once for unsigned, signed and branch cases.
    Bounds prevent field aliasing; the returned bits retain native lookup meanings. -/
theorem resolution_key {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (funct3Bound : (w 10).val ≤ 7) (rightHi : (w 43).val < 65536) :
    ∃ packed : Nat,
      (w 43 + 65536 * w 42 + 131072 * w 38 + 262144 * w 41 + 524288 * w 10).val = packed ∧
      packed / 32768 % 2 = (w 43).val / 32768 ∧
      packed / 65536 % 2 = (w 42).val ∧
      packed / 131072 % 2 = (w 38).val ∧ packed / 262144 % 2 = (w 41).val ∧
      packed / 524288 % 8 = (w 10).val ∧
      (w 38).val ≤ 1 := by
  have oneVal : (1 : ZMod p).val = 1 := ZMod.val_one'' (by omega)
  have values := lookup_values hp h
  have sign := Verification.u16Sign_value (by omega : 65536 ≤ p)
    (Verification.lookup_of_holds h ⟨5, by simp [importedConstraints, FlatOperation.lookups]⟩)
  simp [Expression.eval, Verification.environment] at sign
  have signBound : (w 42).val ≤ 1 := by
    rw [sign.2, ZMod.val_natCast]
    have small : (w 23).val / 32768 ≤ 1 := by omega
    exact (Nat.mod_le _ _).trans small
  have zeroBound : (w 41).val ≤ 1 := by
    rw [values.1]
    split <;> simp [oneVal]
  have borrow := Verification.assertion_of_holds h
    ⟨20, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at borrow
  have bits : w 38 = 0 ∨ w 38 = 1 := by
    simpa [mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] using borrow
  have borrowBound : (w 38).val ≤ 1 := by
    rcases bits with h0 | h1
    · simp [h0]
    · simp [h1, oneVal]
  let packed := (w 43).val + 65536 * (w 42).val + 131072 * (w 38).val +
    262144 * (w 41).val + 524288 * (w 10).val
  have packedBound : packed < 4194304 := by dsimp [packed]; omega
  have key :
      (w 43 + 65536 * w 42 + 131072 * w 38 + 262144 * w 41 + 524288 * w 10).val = packed := by
    have cast : w 43 + 65536 * w 42 + 131072 * w 38 + 262144 * w 41 + 524288 * w 10 =
        (packed : ZMod p) := by
      simp [packed, Nat.cast_add, Nat.cast_mul]
    rw [cast, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_of_lt_of_le packedBound hp)]
  refine ⟨packed, key, ?_, ?_, ?_, ?_, ?_, borrowBound⟩ <;> dsimp [packed] <;> omega

/-- Unsigned resolution selects the already-constrained subtraction borrow. -/
theorem unsigned_resolution {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (funct3 : w 10 = 3)
    (rightHi : (w 27 + w 9).val < 65536) : w 44 = w 38 := by
  have threeVal : (3 : ZMod p).val = 3 := by
    change ((3 : Nat) : ZMod p).val = 3
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have source := Verification.assertion_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected] at source
  have sourceEq : w 43 = w 27 + w 9 := by linear_combination source
  obtain ⟨packed, key, _, _, bit, _, tag, borrowBound⟩ := resolution_key hp h
    (by rw [funct3, threeVal]; decide) (by rw [sourceEq]; exact rightHi)
  have result := (lookup_values hp h).2.2.1
  rw [key] at result
  simp [Verification.conditionalValue, tag, funct3, threeVal, bit] at result
  have bits : (w 38).val = 0 ∨ (w 38).val = 1 := by omega
  have canonical : w 38 = ((w 38).val : ZMod p) := (ZMod.natCast_zmod_val _).symm
  rw [canonical]
  rcases bits with zero | one
  · simpa [zero] using result
  · simpa [one] using result

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

/-- The same bits carry the saved jump link or borrow in a subtraction. -/
theorem arithmetic_carries {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    ∃ c b : Nat, c ≤ 1 ∧ b ≤ 1 ∧ w 37 = (c : ZMod p) ∧ w 38 = (b : ZMod p) := by
  have carry := Verification.assertion_of_holds h
    ⟨19, by simp [importedConstraints, FlatOperation.constraints]⟩
  have borrow := Verification.assertion_of_holds h
    ⟨20, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at carry borrow
  obtain ⟨c, cb, hc⟩ := boolean_nat (x := w 37) (by simpa [mul_eq_zero, sub_eq_add_neg] using carry)
  obtain ⟨b, bb, hb⟩ := boolean_nat (x := w 38) (by simpa [mul_eq_zero, sub_eq_add_neg] using borrow)
  exact ⟨c, b, cb, bb, hc, hb⟩

/-- Shared subtraction relation for comparison and branch selectors. Only SLT
    adds the immediate; branch immediates are reserved for the PC relation. -/
theorem subtraction_equations {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (other : w 11 = 0 ∧ w 12 = 0) (selection : w 13 + w 14 = 1) :
    ∃ c b : Nat, c ≤ 1 ∧ b ≤ 1 ∧ w 37 = (c : ZMod p) ∧ w 38 = (b : ZMod p) ∧
      w 34 + (w 26 + w 8 * w 13) = w 22 + 65536 * c ∧
      (c : ZMod p) + w 35 + (w 27 + w 9 * w 13) = w 23 + 65536 * b := by
  obtain ⟨c, b, cb, bb, hc, hb⟩ := arithmetic_carries h
  have low := Verification.assertion_of_holds h
    ⟨1, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨2, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, other.1, other.2, hc, hb] at low high
  refine ⟨c, b, cb, bb, hc, hb, ?_, ?_⟩
  · linear_combination low - (w 34 + w 26 - w 22 - 65536 * c) * selection
  · linear_combination high - ((c : ZMod p) + w 35 + w 27 - w 23 - 65536 * b) * selection

/-- The comparison branch computes the unsigned borrow, reused by destination proofs. -/
theorem unsigned_borrow {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 38 = 1 ↔ left.value < right.value := by
  obtain ⟨c, b, cb, bb, _, hb, low, high⟩ := subtraction_equations h
    ⟨other.1, other.2.1⟩ (by simp [selected, other.2.2])
  simp only [selected, mul_one] at low high
  have bits : w 38 = 1 ↔ b = 1 := by
    rw [hb]
    have cases : b = 0 ∨ b = 1 := by omega
    rcases cases with rfl | rfl <;> simp
  rw [bits]
  have bounds := local_ranges h
  apply Word.borrow_iff hp leftBound rightBound (remainder := ⟨(w 34).val, (w 35).val⟩)
    ⟨bounds.1, bounds.2.1⟩ cb bb
  · simp only [ZMod.natCast_zmod_val]
    rw [← mapping.1, ← mapping.2.2.1]
    exact low
  · simp only [ZMod.natCast_zmod_val]
    rw [← mapping.2.1, ← mapping.2.2.2]
    exact high

/-- Comparison selection and the destination mask expose the resolution value. -/
theorem comparison_destination {p : Nat} [Fact p.Prime]
    {w : Nat → ZMod p} {output : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (nonzero : w 15 = 0)
    (outputMapping : output.lo = (w 30).val ∧ output.hi = (w 31).val) :
    output.value = (w 44).val := by
  have selectedLow := Verification.assertion_of_holds h
    ⟨8, by simp [importedConstraints, FlatOperation.constraints]⟩
  have selectedHigh := Verification.assertion_of_holds h
    ⟨9, by simp [importedConstraints, FlatOperation.constraints]⟩
  have outputLow := Verification.assertion_of_holds h
    ⟨10, by simp [importedConstraints, FlatOperation.constraints]⟩
  have outputHigh := Verification.assertion_of_holds h
    ⟨11, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected, other.1, other.2.1, nonzero]
    at selectedLow selectedHigh outputLow outputHigh
  have low : w 30 = w 44 := by linear_combination -selectedLow - outputLow
  have high : w 31 = 0 := by linear_combination selectedHigh - outputHigh
  simp [Word.value, outputMapping.1, outputMapping.2, low, high]

/-- Local unsigned destination correctness, including the actual resolution query.
    PC/register effects are composed separately; operand bounds remain interfaces. -/
theorem unsigned_destination {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right output : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (funct3 : w 10 = 3) (nonzero : w 15 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (outputMapping : output.lo = (w 30).val ∧ output.hi = (w 31).val)
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    output.value = if left.value < right.value then 1 else 0 := by
  have rightHi : (w 27 + w 9).val < 65536 := by
    rw [mapping.2.2.2, ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have := rightBound.2; unfold limbBase at this; omega)]
    exact rightBound.2
  have resolved := unsigned_resolution hp h selected funct3 rightHi
  have destination := comparison_destination h selected other nonzero outputMapping
  rw [destination, resolved]
  have comparison := unsigned_borrow (by omega : 196608 < p)
    h selected other mapping leftBound rightBound
  by_cases lt : left.value < right.value
  · have one := comparison.mpr lt
    have oneVal : (1 : ZMod p).val = 1 := ZMod.val_one'' (by omega)
    simp only [if_pos lt]
    simp [one, oneVal]
  · have notOne : w 38 ≠ 1 := fun one => lt (comparison.mp one)
    have flag := Verification.assertion_of_holds h
      ⟨20, by simp [importedConstraints, FlatOperation.constraints]⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero] at flag
    have zero : w 38 = 0 := flag.resolve_right notOne
    simp only [if_neg lt]
    simp [zero]

end Airbender.JumpBranchSlt.Proofs
