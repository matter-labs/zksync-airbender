import Airbender.Review.Word
import Airbender.Proofs.Arithmetic.Limbs

namespace Airbender.Arithmetic

theorem Word.value_lt {word : Word} (h : word.Bounded) : word.value < wordModulus := by
  rcases h with ⟨hl, hh⟩
  unfold Word.value limbBase wordModulus at *
  omega

@[simp] theorem Word.toBitVec_toNat {word : Word} (h : word.Bounded) :
    word.toBitVec.toNat = word.value :=
  Nat.mod_eq_of_lt (Word.value_lt h)

/-- Bounded limbs have a unique encoding as a native Sail word. -/
theorem Word.eq_of_toBitVec_eq {left right : Word}
    (hl : left.Bounded) (hr : right.Bounded) (hv : left.toBitVec = right.toBitVec) :
    left = right := by
  have hn := congrArg BitVec.toNat hv
  simp only [Word.toBitVec_toNat hl, Word.toBitVec_toNat hr] at hn
  have hlimbs := two_limb_encoding_injective hl.1 hr.1 hn
  cases left
  cases right
  rcases hlimbs with ⟨rfl, rfl⟩
  rfl

end Airbender.Arithmetic
