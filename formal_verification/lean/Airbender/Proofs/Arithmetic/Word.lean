import Airbender.Review.Word
import Mathlib.Data.Nat.Basic

namespace Airbender.Arithmetic

theorem Word.value_lt {word : Word} (h : word.Bounded) : word.value < wordModulus := by
  rcases h with ⟨hl, hh⟩
  unfold Word.value limbBase wordModulus at *
  omega

@[simp] theorem Word.toBitVec_toNat {word : Word} (h : word.Bounded) :
    word.toBitVec.toNat = word.value :=
  Nat.mod_eq_of_lt (Word.value_lt h)

end Airbender.Arithmetic
