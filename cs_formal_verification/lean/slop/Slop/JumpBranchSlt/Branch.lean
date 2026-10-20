import Slop.JumpBranchSlt.Signed
import Slop.JumpBranchSlt.PC
import Mathlib.Tactic.IntervalCases

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic

/-- Shared destination mask for branches and jumps writing x0. -/
theorem masked_destination {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (zero : w 15 = 1) : w 30 = 0 ∧ w 31 = 0 := by
  have lo := Verification.assertion_of_holds h
    ⟨10, by simp [importedConstraints, FlatOperation.constraints]⟩
  have hi := Verification.assertion_of_holds h
    ⟨11, by simp [importedConstraints, FlatOperation.constraints]⟩
  simpa [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, zero] using And.intro lo hi

private theorem branch_bits {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 14 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 = (right.lo : ZMod p) ∧ w 27 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    (w 38).val = (if left.value < right.value then 1 else 0) ∧
    (w 41).val = (if left.toBitVec = right.toBitVec then 1 else 0) ∧
    (w 43).val = right.hi := by
  obtain ⟨c, b, cb, bb, _, hb, low, high⟩ := subtraction_equations h
    ⟨other.1, other.2.1⟩ (by simp [selected, other.2.2])
  simp only [other.2.2, mul_zero, add_zero, mapping.1, mapping.2.1,
    mapping.2.2.1, mapping.2.2.2] at low high
  let remainder : Word := ⟨(w 34).val, (w 35).val⟩
  have bounds := local_ranges h
  have remainderBound : remainder.Bounded := ⟨bounds.1, bounds.2.1⟩
  have lowEq : (remainder.lo : ZMod p) + right.lo = left.lo + 65536 * c := by
    simpa only [remainder, ZMod.natCast_zmod_val] using low
  have highEq : (c : ZMod p) + remainder.hi + right.hi = left.hi + 65536 * b := by
    simpa only [remainder, ZMod.natCast_zmod_val] using high
  have borrow := Word.borrow_iff (by omega : 196608 < p)
    leftBound rightBound remainderBound cb bb lowEq highEq
  have subtraction := Word.sub_of_limbs (by omega : 131072 < p)
    leftBound rightBound remainderBound cb bb lowEq highEq
  have oneVal : (1 : ZMod p).val = 1 := ZMod.val_one'' (by omega)
  have bval : (w 38).val = b := by
    rw [hb, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have borrowVal : (w 38).val = if left.value < right.value then 1 else 0 := by
    rw [bval]
    by_cases lt : left.value < right.value
    · simp [lt, borrow.mpr lt]
    · have := mt borrow.mp lt
      simp only [ite_eq_right lt]
      omega
  have sum : (w 34 + w 35).val = remainder.lo + remainder.hi := by
    have cast : w 34 + w 35 = ((remainder.lo + remainder.hi : Nat) : ZMod p) := by
      simp [remainder, Nat.cast_add]
    rw [cast, ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have := remainderBound.1; have := remainderBound.2
      unfold limbBase at *; omega)]
  have zero : (w 34 + w 35).val = 0 ↔ remainder.toBitVec = 0 := by
    rw [sum]
    constructor
    · intro hz
      apply BitVec.eq_of_toNat_eq
      rw [Word.toBitVec_toNat remainderBound]
      change remainder.value = 0
      unfold Word.value limbBase
      omega
    · intro hz
      have value := congrArg BitVec.toNat hz
      rw [Word.toBitVec_toNat remainderBound] at value
      change remainder.value = 0 at value
      unfold Word.value limbBase at value
      omega
  have equal : (w 34 + w 35).val = 0 ↔ left.toBitVec = right.toBitVec := by
    rw [zero, subtraction, BitVec.sub_eq_iff_eq_add]
    simp
  have values := lookup_values hp h
  have zeroVal : (w 41).val = if left.toBitVec = right.toBitVec then 1 else 0 := by
    rw [values.1]
    by_cases eq : left.toBitVec = right.toBitVec
    · simp [equal.mpr eq, eq, oneVal]
    · have hz := mt equal.mp eq
      simp [hz, eq]
  have source := Verification.assertion_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, other.2.2] at source
  have sourceEq : w 43 = w 27 := by linear_combination source
  refine ⟨borrowVal, zeroVal, ?_⟩
  rw [sourceEq, mapping.2.2.2, ZMod.val_natCast, Nat.mod_eq_of_lt (by
    have := rightBound.2; unfold limbBase at this; omega)]

set_option maxHeartbeats 600000 in
/-- Local branch resolution, derived from subtraction and the imported lookup.
    This is not yet an architectural Sail branch/PC soundness theorem. -/
theorem branch_resolution {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 14 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0)
    (funct3Bound : (w 10).val ≤ 7)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 = (right.lo : ZMod p) ∧ w 27 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 45 = ((match (w 10).val with
      | 0 => if left.toBitVec = right.toBitVec then 1 else 0
      | 1 => if left.toBitVec ≠ right.toBitVec then 1 else 0
      | 2 | 4 => if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0
      | 3 | 6 => if left.value < right.value then 1 else 0
      | 5 => if ¬ left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0
      | _ => if ¬ left.value < right.value then 1 else 0 : Nat) : ZMod p) := by
  obtain ⟨borrow, equal, rightHi⟩ := branch_bits hp h selected other mapping leftBound rightBound
  obtain ⟨packed, key, rightBit, leftBit, borrowBit, equalBit, tag, _⟩ :=
    resolution_key hp h funct3Bound (by rw [rightHi]; exact rightBound.2)
  have values := lookup_values hp h
  have leftHi : (w 23).val = left.hi := by
    rw [mapping.2.1, ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have := leftBound.2; unfold limbBase at this; omega)]
  have sign : (w 42).val = left.hi / 32768 := by
    rw [values.2.1, leftHi, ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have := leftBound.2; unfold limbBase at this; omega)]
  have lp : left.hi / 32768 = if left.hi < 32768 then 0 else 1 := by
    have := leftBound.2; unfold limbBase at this
    split <;> omega
  have rp : right.hi / 32768 = if right.hi < 32768 then 0 else 1 := by
    have := rightBound.2; unfold limbBase at this
    split <;> omega
  have result := values.2.2.1
  rw [key] at result
  have taken := Verification.assertion_of_holds h
    ⟨4, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected] at taken
  have takenEq : w 45 = w 44 := by linear_combination -taken
  rw [takenEq]
  convert result using 1
  interval_cases (w 10).val
  all_goals solve
    | (by_cases eq : left.toBitVec = right.toBitVec <;>
        simp [Verification.conditionalValue, tag, equalBit, equal, eq])
    | (by_cases lpos : left.hi < 32768 <;> by_cases rpos : right.hi < 32768 <;>
        by_cases lt : left.value < right.value <;>
        simp [Verification.conditionalValue, tag, rightBit, rightHi, leftBit, sign,
          borrowBit, borrow, lp, rp, lpos, rpos, lt, Word.signed_lt_iff leftBound rightBound])

/-- A selected branch uses its resolved bit for PC selection. Even offsets are
    a decoder obligation; the imported bit-1 check enforces four-byte alignment
    when taken. The final high-PC bound remains a state/ROM obligation. -/
theorem branch_pc {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {initial offset final : Word} (taken : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 14 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0)
    (resolved : w 45 = if taken then 1 else 0)
    (mapping : initial.lo = (w 0).val ∧ initial.hi = (w 1).val ∧
      w 8 = (offset.lo : ZMod p) ∧ w 9 = (offset.hi : ZMod p) ∧
      final.lo = (w 16).val ∧ final.hi = (w 17).val)
    (initialLoBound : initial.lo < limbBase) (initialAligned : initial.lo % 4 = 0)
    (offsetBound : offset.Bounded) (offsetEven : offset.lo % 2 = 0)
    (finalHiBound : final.hi < limbBase) :
    final.toBitVec = (if taken then initial.toBitVec + offset.toBitVec else initial.toBitVec + 4) ∧
      final.toBitVec.toNat % 4 = 0 := by
  have bounds := local_ranges h
  have cleanup := (lookup_values hp h).2.2.2
  obtain ⟨c, b, cb, bb, hc, hb⟩ := pc_carries h
  have low := Verification.assertion_of_holds h
    ⟨5, by simp [importedConstraints, FlatOperation.constraints]⟩
  have high := Verification.assertion_of_holds h
    ⟨6, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected, other.1, other.2.1, other.2.2,
    resolved, hc, hb, mapping.2.2.1, mapping.2.2.2.1] at low high
  have initialLo : w 0 = (initial.lo : ZMod p) := by
    rw [mapping.1]; exact (ZMod.natCast_zmod_val _).symm
  have initialHi : w 1 = (initial.hi : ZMod p) := by
    rw [mapping.2.1]; exact (ZMod.natCast_zmod_val _).symm
  let increment : Word := if taken then offset else ⟨4, 0⟩
  have incrementBound : increment.Bounded := by
    cases taken
    · change (⟨4, 0⟩ : Word).Bounded
      exact ⟨by decide, by decide⟩
    · exact offsetBound
  have lowEq : (initial.lo : ZMod p) + increment.lo = (w 36).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [initialLo] at low
    cases taken <;> simp [increment] at * <;> linear_combination low
  have lowNat : initial.lo + increment.lo = (w 36).val + 65536 * c :=
    bounded_nat_eq (F := ZMod p) (p := p)
      (by have := incrementBound.1; unfold limbBase at *; omega)
      (by have := bounds.2.2.2; unfold limbBase at *; omega)
      (by exact_mod_cast lowEq)
  have aligned : (w 36).val % 4 = 0 := by
    cases taken
    · simp only [increment, Bool.false_eq_true, ↓reduceIte] at lowNat
      omega
    · have checked := Verification.assertion_of_holds h
        ⟨7, by simp [importedConstraints, FlatOperation.constraints]⟩
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment, other.1, other.2.1, resolved] at checked
      have bit1 : (w 36).val / 2 % 2 = 0 := by
        have eq : (((w 36).val / 2 % 2 : Nat) : ZMod p) = 0 := cleanup.1 ▸ checked
        have eqVal := congrArg ZMod.val eq
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by
          have := Nat.mod_lt ((w 36).val / 2) (by decide : 0 < 2); omega)] at eqVal
        simpa using eqVal
      simp only [increment, ↓reduceIte] at lowNat
      omega
  have finalLo : final.lo = (w 36).val := by
    rw [mapping.2.2.2.2.1, cleanup.2, aligned, Nat.sub_zero, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by have := bounds.2.2.2; unfold limbBase at this; omega)]
  have finalHi : w 17 = (final.hi : ZMod p) := by
    rw [mapping.2.2.2.2.2]; exact (ZMod.natCast_zmod_val _).symm
  have finalBound : final.Bounded := ⟨finalLo ▸ bounds.2.2.2, finalHiBound⟩
  have result := Word.add_of_limbs (by omega : 196608 < p)
    (left := initial) (right := ⟨0, 0⟩) (immediate := increment) (output := final)
    ⟨initialLoBound, mapping.2.1 ▸ bounds.2.2.1⟩ (by constructor <;> decide)
    incrementBound finalBound (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa [finalLo] using lowEq)
    (by
      rw [initialHi, finalHi] at high
      cases taken <;> simp [increment] at * <;> linear_combination high)
  constructor
  · cases taken <;> simpa [increment, Word.toBitVec, Word.value, limbBase] using result
  · rw [Word.toBitVec_toNat finalBound]
    unfold Word.value limbBase
    rw [finalLo]
    omega

end Airbender.JumpBranchSlt.Proofs
