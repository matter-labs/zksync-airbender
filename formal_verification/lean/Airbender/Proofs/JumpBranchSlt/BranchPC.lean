import Airbender.Proofs.JumpBranchSlt.Target

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Verification

/-- Native branch PC selection preserves RV32 wrap. Actual scalar queries bound
    both candidates; original decoded parity and the taken bit-one assertion
    prevent cleanup from silently rounding a taken target. -/
theorem branch_pc {w : Nat → ZMod mersenne31Modulus} {initial offset : Word}
    (taken : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 21 = 1) (other : w 17 = 0 ∧ w 18 = 0 ∧ w 19 = 0 ∧ w 20 = 0)
    (resolved : w 46 = if taken then 1 else 0)
    (mapping : initial.lo = (w 0).val ∧ initial.hi = (w 1).val ∧
      w 9 = (offset.lo : ZMod mersenne31Modulus) ∧ w 10 = (offset.hi : ZMod mersenne31Modulus))
    (initialBound : initial.Bounded) (initialAligned : initial.lo % 4 = 0)
    (offsetBound : offset.Bounded) (offsetEven : offset.lo % 2 = 0) :
    (Word.mk (w 13).val (w 14).val).toBitVec =
      (if taken then initial.toBitVec + offset.toBitVec else initial.toBitVec + 4) ∧
    (Word.mk (w 13).val (w 14).val).toBitVec.toNat % 4 = 0 := by
  have cleanup := fixed_effects h
  obtain ⟨c,b,cb,bb,hc,hb⟩ := pc_carries h
  have notTaken := assertion_of_holds h ⟨24,by rw [constraint_count]; decide⟩
  have chosen := assertion_of_holds h ⟨25,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,selected] at notTaken chosen
  have total : w 45 + w 46 = 1 := by linear_combination -notTaken-chosen
  have complement : w 45 = if taken then 0 else 1 := by
    rw [resolved] at total
    cases taken <;> simp only [Bool.false_eq_true,if_false,if_true] at total ⊢
    all_goals linear_combination total
  have low := assertion_of_holds h ⟨31,by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨32,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    other.1,other.2.1,other.2.2.1,other.2.2.2,complement,resolved,hc,hb,
    mapping.2.2.1,mapping.2.2.2] at low high
  have initialLo : w 0 = (initial.lo : ZMod mersenne31Modulus) := by
    rw [mapping.1]; exact (ZMod.natCast_zmod_val _).symm
  have initialHi : w 1 = (initial.hi : ZMod mersenne31Modulus) := by
    rw [mapping.2.1]; exact (ZMod.natCast_zmod_val _).symm
  let increment : Word := if taken then offset else ⟨4,0⟩
  have incrementBound : increment.Bounded := by
    cases taken
    · change (⟨4,0⟩ : Word).Bounded
      exact ⟨by decide,by decide⟩
    · exact offsetBound
  have lowEq : (initial.lo : ZMod mersenne31Modulus) + increment.lo = (w 42).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [initialLo] at low
    cases taken <;> simp [increment] at low ⊢ <;> linear_combination low
  have highEq : (c : ZMod mersenne31Modulus) + initial.hi + increment.hi = (w 43).val + 65536 * b := by
    simp only [ZMod.natCast_zmod_val]
    rw [initialHi] at high
    cases taken <;> simp [increment] at high ⊢ <;> linear_combination high
  let raw : Word := ⟨(w 42).val,(w 43).val⟩
  have rawBound : raw.Bounded :=
    ⟨range16_bound (lookup_of_holds h ⟨4,by rw [lookup_count]; decide⟩),candidate_high_bound h⟩
  have lowNat : initial.lo + increment.lo = (w 42).val + 65536 * c :=
    bounded_nat_eq (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
      (by have := initialBound.1; have := incrementBound.1; dsimp [limbBase] at * ; change _ < 2147483647; omega)
      (by have := rawBound.1; dsimp [raw,limbBase] at * ; change _ < 2147483647; omega)
      (by exact_mod_cast lowEq)
  have aligned : (w 42).val % 4 = 0 := by
    cases taken
    · simp only [increment,Bool.false_eq_true,if_false] at lowNat
      omega
    · have checked := assertion_of_holds h ⟨26,by rw [constraint_count]; decide⟩
      simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
        other.1,other.2.1,resolved] at checked
      have bit1 : (w 42).val / 2 % 2 = 0 := by
        have eq : (((w 42).val / 2 % 2 : Nat) : ZMod mersenne31Modulus) = 0 := cleanup.bit1 ▸ checked
        have value := congrArg ZMod.val eq
        rw [ZMod.val_natCast_of_lt (by
          have := Nat.mod_lt ((w 42).val / 2) (by decide : 0 < 2)
          change _ < 2147483647; omega)] at value
        simpa using value
      simp only [increment,if_true] at lowNat
      omega
  have cleanSame : w 48 = w 42 := by
    rw [cleanup.cleaned]
    have same : 4 * ((w 42).val / 4) = (w 42).val := by omega
    rw [same,ZMod.natCast_zmod_val]
  have finalLo : w 13 = w 42 := by
    have eq := assertion_of_holds h ⟨27,by rw [constraint_count]; decide⟩
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
      other.1,other.2.1,other.2.2.1,other.2.2.2,cleanSame] at eq
    linear_combination -eq + w 42 * total
  have finalHi : w 14 = w 43 := by
    have eq := assertion_of_holds h ⟨28,by rw [constraint_count]; decide⟩
    simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
      other.1,other.2.1,other.2.2.1,other.2.2.2] at eq
    linear_combination -eq + w 43 * total
  have sum := Word.add_of_limbs (by decide : 196608 < mersenne31Modulus)
    (left := initial) (right := ⟨0,0⟩) (immediate := increment) (output := raw)
    initialBound (by constructor <;> decide) incrementBound rawBound
    (Nat.le_trans cb (by decide)) (Nat.le_trans bb (by decide))
    (by simpa [raw] using lowEq) (by simpa [raw] using highEq)
  rw [finalLo,finalHi]
  constructor
  · cases taken <;> simpa [increment,raw,Word.toBitVec,Word.value,limbBase] using sum
  · rw [Word.toBitVec_toNat rawBound]
    dsimp [raw,Word.value,limbBase]
    omega

end Airbender.JumpBranchSlt.Proofs
