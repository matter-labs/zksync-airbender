import Airbender.Proofs.JumpBranchSlt.Comparison
import Airbender.Review.Circuits.JumpBranchSlt.Branch

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Verification

/-- Original subtraction, borrow and zero-remainder lifting at native v2 columns.
    Actual inverse equations identify equality, including two zero limbs. -/
theorem branch_flags {w : Nat → ZMod mersenne31Modulus} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 21 = 1) (other : w 17 = 0 ∧ w 18 = 0 ∧ w 19 = 0 ∧ w 20 = 0)
    (mapping : w 22 = (left.lo : ZMod mersenne31Modulus) ∧ w 23 = (left.hi : ZMod mersenne31Modulus) ∧
      w 24 = (right.lo : ZMod mersenne31Modulus) ∧ w 25 = (right.hi : ZMod mersenne31Modulus))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 28 = ((if left.value < right.value then 1 else 0 : Nat) : ZMod mersenne31Modulus) ∧
    w 29 = ((if left.toBitVec = right.toBitVec then 1 else 0 : Nat) : ZMod mersenne31Modulus) ∧
    w 31 = (if left.hi < 32768 then 1 else 0) ∧
    w 33 = (if right.hi < 32768 then 1 else 0) := by
  obtain ⟨c,b,cb,bb,hc,hb⟩ := arithmetic_carries h
  have low := assertion_of_holds h ⟨29,by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨30,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    selected,other.1,other.2.1,other.2.2.1,other.2.2.2,hc,hb,
    mapping.1,mapping.2.1,mapping.2.2.1,mapping.2.2.2] at low high
  let remainder : Word := ⟨(w 26).val,(w 27).val⟩
  have bounded : remainder.Bounded :=
    ⟨range16_bound (lookup_of_holds h ⟨0,by rw [lookup_count]; decide⟩),
      range16_bound (lookup_of_holds h ⟨1,by rw [lookup_count]; decide⟩)⟩
  have lowEq : (remainder.lo : ZMod mersenne31Modulus) + right.lo = left.lo + 65536*c := by
    simp only [remainder,ZMod.natCast_zmod_val]
    linear_combination low
  have highEq : (c : ZMod mersenne31Modulus) + remainder.hi + right.hi = left.hi + 65536*b := by
    simp only [remainder,ZMod.natCast_zmod_val]
    linear_combination high
  have borrow := Word.borrow_iff (by decide : 196608 < mersenne31Modulus)
    leftBound rightBound bounded cb bb lowEq highEq
  have subtraction := Word.sub_of_limbs (by decide : 131072 < mersenne31Modulus)
    leftBound rightBound bounded cb bb lowEq highEq
  have borrowEq : w 28 = ((if left.value < right.value then 1 else 0 : Nat) : ZMod mersenne31Modulus) := by
    rw [hb]
    by_cases lt : left.value < right.value
    · simp [lt,borrow.mpr lt]
    · have := mt borrow.mp lt
      have zero : b = 0 := by omega
      simp [lt,zero]
  have sum : (w 26 + w 27).val = remainder.lo + remainder.hi := by
    have cast : w 26 + w 27 = ((remainder.lo+remainder.hi : Nat) : ZMod mersenne31Modulus) := by
      simp [remainder,Nat.cast_add]
    rw [cast,ZMod.val_natCast_of_lt (by
      have := bounded.1; have := bounded.2; dsimp [limbBase] at *; change _ < 2147483647; omega)]
  have zero : (w 26+w 27).val = 0 ↔ remainder.toBitVec = 0 := by
    rw [sum]
    constructor
    · intro hz
      apply BitVec.eq_of_toNat_eq
      rw [Word.toBitVec_toNat bounded]
      change remainder.value = 0
      dsimp [Word.value,limbBase] at *
      omega
    · intro hz
      have value := congrArg BitVec.toNat hz
      rw [Word.toBitVec_toNat bounded] at value
      change remainder.value = 0 at value
      dsimp [Word.value,limbBase] at value
      omega
  have equal : (w 26+w 27).val = 0 ↔ left.toBitVec = right.toBitVec := by
    rw [zero,subtraction,BitVec.sub_eq_iff_eq_add]
    simp
  have inverse := assertion_of_holds h ⟨16,by rw [constraint_count]; decide⟩
  have product := assertion_of_holds h ⟨17,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment] at inverse product
  have equalEq : w 29 = ((if left.toBitVec = right.toBitVec then 1 else 0 : Nat) : ZMod mersenne31Modulus) := by
    by_cases eq : left.toBitVec = right.toBitVec
    · have sumZero : w 26+w 27 = 0 := by
        calc w 26+w 27 = (((w 26+w 27).val : Nat) : ZMod mersenne31Modulus) := (ZMod.natCast_zmod_val _).symm
             _ = 0 := by rw [equal.mpr eq]; simp
      simp only [if_pos eq,Nat.cast_one]
      linear_combination inverse - w 30 * sumZero
    · have sumNE : w 26+w 27 ≠ 0 := by
        intro hz; exact eq (equal.mp (by rw [hz]; rfl))
      have mul : (w 26+w 27)*w 29 = 0 := by linear_combination product
      simpa [eq] using (mul_eq_zero.mp mul).resolve_left sumNE
  have lp := assertion_of_holds h ⟨18,by rw [constraint_count]; decide⟩
  have rp := assertion_of_holds h ⟨19,by rw [constraint_count]; decide⟩
  have lb := assertion_of_holds h ⟨6,by rw [constraint_count]; decide⟩
  have rb := assertion_of_holds h ⟨7,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    selected,other.1,other.2.1,other.2.2.1,other.2.2.2,mapping.2.1,mapping.2.2.2] at lp rp lb rb
  have leftEq : (left.hi : ZMod mersenne31Modulus)-32768-w 32+65536*w 31 = 0 := by linear_combination lp
  have rightEq : (right.hi : ZMod mersenne31Modulus)-32768-w 34+65536*w 33 = 0 := by linear_combination rp
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
  exact ⟨borrowEq,equalEq,leftSign,rightSign⟩

/-- Actual conditional-table membership resolves every original branch tag. -/
theorem branch_resolution {w : Nat → ZMod mersenne31Modulus} {left right : Word}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 21 = 1) (other : w 17 = 0 ∧ w 18 = 0 ∧ w 19 = 0 ∧ w 20 = 0)
    (tags : (w 11).val ∈ [0,1,4,5,6,7])
    (mapping : w 22 = (left.lo : ZMod mersenne31Modulus) ∧ w 23 = (left.hi : ZMod mersenne31Modulus) ∧
      w 24 = (right.lo : ZMod mersenne31Modulus) ∧ w 25 = (right.hi : ZMod mersenne31Modulus))
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    w 35 = if branchCondition (w 11).val left right then 1 else 0 := by
  obtain ⟨borrow,equal,leftSign,rightSign⟩ := branch_flags h selected other mapping leftBound rightBound
  let key := (if left.value < right.value then 1 else 0) +
    2*(if left.toBitVec = right.toBitVec then 1 else 0) +
    4*(if left.hi < 32768 then 0 else 1) + 8*(if right.hi < 32768 then 0 else 1)
  have keyBound : key < 16 := by dsimp [key]; split_ifs <;> omega
  have keyEq : controlBits w = (key : ZMod mersenne31Modulus) := by
    dsimp [controlBits,key]
    rw [borrow,equal,leftSign,rightSign]
    split_ifs <;> norm_num
  have keyVal : (controlBits w).val = key := by
    rw [keyEq,ZMod.val_natCast_of_lt (lt_trans keyBound (by decide : 16 < mersenne31Modulus))]
  have result := (fixed_effects h).control
  rw [keyVal] at result
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at tags
  rcases tags with tag | tag | tag | tag | tag | tag
  all_goals rw [tag] at result ⊢
  all_goals by_cases eq : left.toBitVec = right.toBitVec <;>
    by_cases lp : left.hi < 32768 <;> by_cases rp : right.hi < 32768 <;>
    by_cases lt : left.value < right.value <;>
    first
    | simpa [branchCondition,key,controlFlag,eq,lp,rp,lt,Word.signed_lt_iff leftBound rightBound] using result
    | have same : left = right := Word.eq_of_value leftBound rightBound (by
        have values := congrArg BitVec.toNat eq
        simpa only [Word.toBitVec_toNat leftBound,Word.toBitVec_toNat rightBound] using values)
      subst right
      simp_all

/-- Native branch routing retains the exact taken/complement bits and writes zero,
    independently of the external x0 flag. -/
theorem branch_effects {w : Nat → ZMod mersenne31Modulus} (condition : Bool)
    (h : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (selected : w 21 = 1) (other : w 17 = 0 ∧ w 18 = 0 ∧ w 19 = 0 ∧ w 20 = 0)
    (resolved : w 35 = if condition then 1 else 0) :
    (w 46).val = (if condition then 1 else 0) ∧
    (w 45).val = (if condition then 0 else 1) ∧
    (Word.mk (w 38).val (w 39).val).value = 0 := by
  have notTaken := assertion_of_holds h ⟨24,by rw [constraint_count]; decide⟩
  have taken := assertion_of_holds h ⟨25,by rw [constraint_count]; decide⟩
  have link := assertion_of_holds h ⟨20,by rw [constraint_count]; decide⟩
  have comparison := assertion_of_holds h ⟨21,by rw [constraint_count]; decide⟩
  have low := assertion_of_holds h ⟨22,by rw [constraint_count]; decide⟩
  have high := assertion_of_holds h ⟨23,by rw [constraint_count]; decide⟩
  simp [importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    selected,other.1,other.2.1,other.2.2.1,other.2.2.2] at notTaken taken link comparison low high
  rw [link,comparison] at low
  rw [link] at high
  have lo : w 38 = 0 := by linear_combination -low
  have hi : w 39 = 0 := by linear_combination -high
  rw [resolved] at notTaken taken
  have nt : w 45 = if condition then 0 else 1 := by
    cases condition <;> simp only [Bool.false_eq_true,if_false,if_true] at notTaken ⊢
    all_goals linear_combination -notTaken
  have tk : w 46 = if condition then 1 else 0 := by
    cases condition <;> simp only [Bool.false_eq_true,if_false,if_true] at taken ⊢
    all_goals linear_combination -taken
  rw [nt,tk,lo,hi]
  cases condition <;> decide

end Airbender.JumpBranchSlt.Proofs
