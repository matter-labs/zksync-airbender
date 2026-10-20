import Slop.JumpBranchSlt
import Slop.Arithmetic.Comparison

namespace Airbender.JumpBranchSlt.Proofs
open Airbender.Arithmetic

/-- The imported signed-resolution query agrees with native signed bitvector
    ordering. The same borrow and packed-key proof serves both immediate forms. -/
theorem signed_resolution {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (funct3 : w 10 = 2)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 44 = ((if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0 : Nat) : ZMod p) := by
  have twoVal : (2 : ZMod p).val = 2 := by
    change ((2 : Nat) : ZMod p).val = 2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have leftHi : (w 23).val = left.hi := by
    rw [mapping.2.1, ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have := leftBound.2; unfold limbBase at this; omega)]
  have rightHi : (w 27 + w 9).val = right.hi := by
    rw [mapping.2.2.2, ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have := rightBound.2; unfold limbBase at this; omega)]
  have source := Verification.assertion_of_holds h
    ⟨3, by simp [importedConstraints, FlatOperation.constraints]⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected] at source
  have sourceEq : w 43 = w 27 + w 9 := by linear_combination source
  obtain ⟨packed, key, rightBit, leftBit, borrowBit, _, tag, borrowBound⟩ :=
    resolution_key hp h (by rw [funct3, twoVal]; decide)
      (by rw [sourceEq, rightHi]; exact rightBound.2)
  rw [sourceEq] at rightBit
  have values := lookup_values hp h
  have sign : (w 42).val = left.hi / 32768 := by
    rw [values.2.1, leftHi, ZMod.val_natCast, Nat.mod_eq_of_lt (by
      have := leftBound.2; unfold limbBase at this; omega)]
  have unsigned := unsigned_borrow (by omega : 196608 < p)
    h selected other mapping leftBound rightBound
  have oneVal : (1 : ZMod p).val = 1 := ZMod.val_one'' (by omega)
  have canonical : w 38 = ((w 38).val : ZMod p) := (ZMod.natCast_zmod_val _).symm
  have borrow : (w 38).val = if left.value < right.value then 1 else 0 := by
    by_cases lt : left.value < right.value
    · simp [lt, unsigned.mpr lt, oneVal]
    · have notOne : (w 38).val ≠ 1 := by
        intro eq
        apply lt
        apply unsigned.mp
        simpa [eq] using canonical
      simp only [if_neg lt]
      omega
  have result := values.2.2.1
  rw [key] at result
  have lp : left.hi / 32768 = if left.hi < 32768 then 0 else 1 := by
    have := leftBound.2
    unfold limbBase at this
    split <;> omega
  have rp : right.hi / 32768 = if right.hi < 32768 then 0 else 1 := by
    have := rightBound.2
    unfold limbBase at this
    split <;> omega
  convert result using 1
  by_cases lpos : left.hi < 32768 <;> by_cases rpos : right.hi < 32768 <;>
    by_cases lt : left.value < right.value <;>
    simp [Verification.conditionalValue, tag, funct3, twoVal, rightBit, rightHi,
      leftBit, sign, borrowBit, borrow, lp, rp, lpos, rpos, lt,
      Word.signed_lt_iff leftBound rightBound]

theorem signed_destination {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p} {left right output : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 13 = 1) (other : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0)
    (funct3 : w 10 = 2) (nonzero : w 15 = 0)
    (mapping : w 22 = (left.lo : ZMod p) ∧ w 23 = (left.hi : ZMod p) ∧
      w 26 + w 8 = (right.lo : ZMod p) ∧ w 27 + w 9 = (right.hi : ZMod p))
    (outputMapping : output.lo = (w 30).val ∧ output.hi = (w 31).val)
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    output.value = if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0 := by
  have resolution := signed_resolution hp h selected other funct3 mapping leftBound rightBound
  rw [comparison_destination h selected other nonzero outputMapping, resolution]
  split
  · simpa only [Nat.cast_one] using
      (show (1 : ZMod p).val = 1 from ZMod.val_one'' (by omega))
  · simp

end Airbender.JumpBranchSlt.Proofs
