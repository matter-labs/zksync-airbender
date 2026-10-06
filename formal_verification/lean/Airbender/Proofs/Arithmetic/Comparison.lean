import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Arithmetic

/-- Native signed bitvector decoding from the two-limb representation. -/
theorem Word.toInt_of_limbs {word : Word} (bound : word.Bounded) :
    word.toBitVec.toInt = if word.hi < 32768 then (word.value : Int)
      else (word.value : Int) - 4294967296 := by
  rw [BitVec.toInt_eq_toNat_cond, Word.toBitVec_toNat bound]
  have threshold : 2 * word.value < 2 ^ 32 ↔ word.hi < 32768 := by
    have lo := bound.1
    unfold Word.value limbBase at *
    omega
  simp only [threshold]
  norm_num

/-- Sign adjustment for native signed ordering, reused by comparison lookups. -/
theorem Word.signed_lt_iff {left right : Word}
    (leftBound : left.Bounded) (rightBound : right.Bounded) :
    (left.toBitVec.toInt < right.toBitVec.toInt) ↔
      if left.hi < 32768 then right.hi < 32768 ∧ left.value < right.value
      else right.hi < 32768 ∨ left.value < right.value := by
  rw [Word.toInt_of_limbs leftBound, Word.toInt_of_limbs rightBound]
  have lv := Word.value_lt leftBound
  have rv := Word.value_lt rightBound
  have leftHalf : left.value < 2147483648 ↔ left.hi < 32768 := by
    have := leftBound.1
    unfold Word.value limbBase at *
    omega
  have rightHalf : right.value < 2147483648 ↔ right.hi < 32768 := by
    have := rightBound.1
    unfold Word.value limbBase at *
    omega
  unfold wordModulus at lv rv
  by_cases lp : left.hi < 32768 <;> by_cases rp : right.hi < 32768 <;>
    simp only [lp, rp, if_true, if_false, true_and, false_and, true_or, false_or,
      iff_false, iff_true] <;> omega

end Airbender.Arithmetic
