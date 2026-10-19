import Airbender.Proofs.JumpBranchSlt.Link
import Airbender.Proofs.Arithmetic.Comparison

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Verification

/-- Original subtraction/borrow lifting, with v2 register/immediate selectors. -/
theorem comparison_borrow {w : Nat → ZMod mersenne31Modulus} {left right : Word}
    (immediate : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 19 = (if immediate then 0 else 1) ∧ w 20 = (if immediate then 1 else 0))
    (other : w 17 = 0 ∧ w 18 = 0 ∧ w 21 = 0)
    (mapping : w 22 = (left.lo : ZMod mersenne31Modulus) ∧ w 23 = (left.hi : ZMod mersenne31Modulus) ∧
      w (if immediate then 9 else 24) = (right.lo : ZMod mersenne31Modulus) ∧
      w (if immediate then 10 else 25) = (right.hi : ZMod mersenne31Modulus))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    ∃ b : Nat, b ≤ 1 ∧ w 28 = (b : ZMod mersenne31Modulus) ∧
      b = if left.value < right.value then 1 else 0 := by
  obtain ⟨c,b,cb,bb,hc,hb⟩ := arithmetic_carries h
  have low := assertion_of_holds h ⟨29, by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨30, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, environment,
    other.1,other.2.1,other.2.2,hc,hb] at low high
  have lowEq : ((w 26).val : ZMod mersenne31Modulus) + right.lo = left.lo + 65536*c := by
    simp only [ZMod.natCast_zmod_val]
    rw [← mapping.1]
    cases immediate <;> simp only [Bool.false_eq_true,if_false,if_true] at mapping ⊢
    all_goals simp [selected.1,selected.2,mapping.2.2.1] at low; linear_combination low
  have highEq : (c : ZMod mersenne31Modulus) + (w 27).val + right.hi = left.hi + 65536*b := by
    simp only [ZMod.natCast_zmod_val]
    rw [← mapping.2.1]
    cases immediate <;> simp only [Bool.false_eq_true,if_false,if_true] at mapping ⊢
    all_goals simp [selected.1,selected.2,mapping.2.2.2] at high; linear_combination high
  have remainderBound : (Word.mk (w 26).val (w 27).val).Bounded :=
    ⟨range16_bound (lookup_of_holds h ⟨0,by rw [lookup_count]; decide⟩),
      range16_bound (lookup_of_holds h ⟨1,by rw [lookup_count]; decide⟩)⟩
  have borrow := Word.borrow_iff (by decide : 196608 < mersenne31Modulus)
    leftBound rightBound remainderBound cb bb lowEq highEq
  refine ⟨b,bb,hb,?_⟩
  by_cases lt : left.value < right.value
  · simp [lt,borrow.mpr lt]
  · have := mt borrow.mp lt
    simp only [if_neg lt]
    omega

/-- The native high-limb shift uses a positive flag, complementary to sign. -/
theorem positive_high {hi shifted flag : ZMod mersenne31Modulus} {high : Nat}
    (bound : high < 65536) (mapping : hi = (high : ZMod mersenne31Modulus))
    (range : shifted.val < 65536) (bit : flag = 0 ∨ flag = 1)
    (equation : hi - 32768 - shifted + 65536*flag = 0) :
    flag = if high < 32768 then 1 else 0 := by
  have shiftedEq : shifted = (shifted.val : ZMod mersenne31Modulus) :=
    (ZMod.natCast_zmod_val _).symm
  rw [mapping,shiftedEq] at equation
  rcases bit with zero | one
  · have eq : (high : ZMod mersenne31Modulus) = shifted.val + 32768 := by
      rw [zero] at equation
      linear_combination equation
    have natural : high = shifted.val + 32768 := bounded_nat_eq
      (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
      (by change _ < 2147483647; omega) (by change _ < 2147483647; omega)
      (by exact_mod_cast eq)
    simp [zero,show ¬high < 32768 by omega]
  · have eq : (high : ZMod mersenne31Modulus) + 32768 = shifted.val := by
      rw [one] at equation
      linear_combination equation
    have natural : high + 32768 = shifted.val := bounded_nat_eq
      (F := ZMod mersenne31Modulus) (p := mersenne31Modulus)
      (by change _ < 2147483647; omega) (by change _ < 2147483647; omega)
      (by exact_mod_cast eq)
    simp [one,show high < 32768 by omega]

/-- The native inverse equations derive the equality bit's Booleanity. -/
theorem comparison_zero_flag {w : Nat → ZMod mersenne31Modulus}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints) :
    ∃ e : Nat, e ≤ 1 ∧ w 29 = (e : ZMod mersenne31Modulus) := by
  have inverse := assertion_of_holds h ⟨16,by rw [constraint_count]; decide⟩
  have zero := assertion_of_holds h ⟨17,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at inverse zero
  by_cases sum : w 26 + w 27 = 0
  · refine ⟨1,by decide,?_⟩
    linear_combination inverse - w 30 * sum
  · refine ⟨0,by decide,?_⟩
    have product : (w 26 + w 27)*w 29 = 0 := by linear_combination zero
    exact (mul_eq_zero.mp product).resolve_left sum

/-- Exact signed/unsigned native resolution for either comparison form. -/
theorem comparison_resolution {w : Nat → ZMod mersenne31Modulus} {left right : Word}
    (immediate signed : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 19 = (if immediate then 0 else 1) ∧ w 20 = (if immediate then 1 else 0))
    (other : w 17 = 0 ∧ w 18 = 0 ∧ w 21 = 0)
    (tag : w 11 = if signed then 2 else 3)
    (mapping : w 22 = (left.lo : ZMod mersenne31Modulus) ∧ w 23 = (left.hi : ZMod mersenne31Modulus) ∧
      w (if immediate then 9 else 24) = (right.lo : ZMod mersenne31Modulus) ∧
      w (if immediate then 10 else 25) = (right.hi : ZMod mersenne31Modulus))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 35 = ((if signed then
      (if left.toBitVec.toInt < right.toBitVec.toInt then 1 else 0)
      else (if left.value < right.value then 1 else 0) : Nat) : ZMod mersenne31Modulus) := by
  obtain ⟨b,bb,hb,borrow⟩ := comparison_borrow immediate h selected other mapping leftBound rightBound
  obtain ⟨e,eb,he⟩ := comparison_zero_flag h
  have lp := assertion_of_holds h ⟨18,by rw [constraint_count]; decide⟩
  have rp := assertion_of_holds h ⟨19,by rw [constraint_count]; decide⟩
  have lb := assertion_of_holds h ⟨6,by rw [constraint_count]; decide⟩
  have rb := assertion_of_holds h ⟨7,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    other.1,other.2.1,other.2.2] at lp rp lb rb
  have leftEq : (left.hi : ZMod mersenne31Modulus) - 32768 - w 32 + 65536*w 31 = 0 := by
    rw [← mapping.2.1]
    cases immediate <;> simp [selected.1,selected.2] at lp <;> linear_combination lp
  have rightEq : (right.hi : ZMod mersenne31Modulus) - 32768 - w 34 + 65536*w 33 = 0 := by
    cases immediate <;> simp only [Bool.false_eq_true,if_false,if_true] at mapping
    all_goals rw [← mapping.2.2.2]; simp [selected.1,selected.2] at rp; linear_combination rp
  have leftSign := positive_high leftBound.2 rfl
    (range16_bound (lookup_of_holds h ⟨2,by rw [lookup_count]; decide⟩))
    (by
      obtain ⟨n,nb,eq⟩ := boolean_nat (x := w 31) (by convert lb using 1; ring)
      have cases : n = 0 ∨ n = 1 := by omega
      rcases cases with rfl | rfl <;> simp [eq]) leftEq
  have rightSign := positive_high rightBound.2 rfl
    (range16_bound (lookup_of_holds h ⟨3,by rw [lookup_count]; decide⟩))
    (by
      obtain ⟨n,nb,eq⟩ := boolean_nat (x := w 33) (by convert rb using 1; ring)
      have cases : n = 0 ∨ n = 1 := by omega
      rcases cases with rfl | rfl <;> simp [eq]) rightEq
  let key := b + 2*e + 4*(if left.hi < 32768 then 0 else 1) + 8*(if right.hi < 32768 then 0 else 1)
  have keyBound : key < 16 := by dsimp [key]; split_ifs <;> omega
  have keyEq : controlBits w = (key : ZMod mersenne31Modulus) := by
    dsimp [controlBits,key]
    rw [hb,he,leftSign,rightSign]
    split_ifs <;> norm_num <;> ring
  have keyVal : (controlBits w).val = key := by
    rw [keyEq,ZMod.val_natCast_of_lt (lt_trans keyBound (by decide : 16 < mersenne31Modulus))]
  have twoVal : (2 : ZMod mersenne31Modulus).val = 2 := by decide
  have threeVal : (3 : ZMod mersenne31Modulus).val = 3 := by decide
  have result := (fixed_effects h).control
  rw [keyVal,tag] at result
  have eqCases : e = 0 ∨ e = 1 := by omega
  rcases eqCases with rfl | rfl
  all_goals cases signed
  all_goals by_cases lpos : left.hi < 32768 <;> by_cases rpos : right.hi < 32768 <;>
    by_cases lt : left.value < right.value <;>
    simpa [key,controlFlag,borrow,lpos,rpos,lt,twoVal,threeVal,Word.signed_lt_iff leftBound rightBound] using result

/-- Actual native comparison writes retain the external decoder's x0 mask. -/
theorem comparison_destination {w : Nat → ZMod mersenne31Modulus}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 19 + w 20 = 1) (other : w 17 = 0 ∧ w 18 = 0)
    (flag : w 8 = 0 ∨ w 8 = 1) :
    (Word.mk (w 38).val (w 39).val).value = if w 8 = 1 then 0 else (w 35).val := by
  have link := assertion_of_holds h ⟨20,by rw [constraint_count]; decide⟩
  have comparison := assertion_of_holds h ⟨21,by rw [constraint_count]; decide⟩
  have low := assertion_of_holds h ⟨22,by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨23,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    other.1,other.2] at link comparison low high
  have route : w 37 = 1 - w 8 := by linear_combination -comparison + (1-w 8)*selected
  rw [link] at low high
  rw [route] at low
  rcases flag with zero | one
  · have lowEq : w 38 = w 35 := by rw [zero] at low; linear_combination -low
    have highEq : w 39 = 0 := by linear_combination -high
    simp [lowEq,highEq,zero,Word.value]
  · have lowEq : w 38 = 0 := by rw [one] at low; linear_combination -low
    have highEq : w 39 = 0 := by linear_combination -high
    simp [lowEq,highEq,one,Word.value]

end Airbender.JumpBranchSlt.Proofs
