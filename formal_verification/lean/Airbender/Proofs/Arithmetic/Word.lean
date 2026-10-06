import Airbender.Review.Word
import Airbender.Proofs.Arithmetic.Lemmas
import Mathlib.Data.Nat.Basic

namespace Airbender.Arithmetic

theorem Word.value_lt {word : Word} (h : word.Bounded) : word.value < wordModulus := by
  rcases h with ⟨hl, hh⟩
  unfold Word.value limbBase wordModulus at *
  omega

@[simp] theorem Word.toBitVec_toNat {word : Word} (h : word.Bounded) :
    word.toBitVec.toNat = word.value :=
  Nat.mod_eq_of_lt (Word.value_lt h)

/-- Reuse word encoding after proving a natural-value increment. -/
theorem Word.toBitVec_add_of_value {initial final : Word} {increment : Nat}
    (h : final.value = initial.value + increment) :
    final.toBitVec = initial.toBitVec + BitVec.ofNat 32 increment := by
  simp only [Word.toBitVec, h, BitVec.ofNat_add]

/-- Shared lifting of a small word increment with no high-limb wrap carry. -/
theorem Word.increment_of_limbs {p : Nat} [Fact p.Prime]
    (hp : 131072 < p) {initial final : Word} {increment carry : Nat}
    (incrementBound : increment ≤ limbBase) (carryBound : carry ≤ 1)
    (initialBounds : initial.Bounded) (finalBounds : final.Bounded)
    (low : (initial.lo : ZMod p) + increment = final.lo + 65536 * carry)
    (high : (initial.hi : ZMod p) + carry = final.hi) :
    final.value = initial.value + increment ∧ initial.value + increment < wordModulus ∧
      final.toBitVec = initial.toBitVec + BitVec.ofNat 32 increment := by
  have il := initialBounds.1
  have ih := initialBounds.2
  have fl := finalBounds.1
  have fh := finalBounds.2
  unfold limbBase at il ih fl fh incrementBound
  have lowNat : initial.lo + increment = final.lo + 65536 * carry :=
    bounded_nat_eq (F := ZMod p) (p := p)
      (by omega) (by omega) (by exact_mod_cast low)
  have highNat : initial.hi + carry = final.hi :=
    bounded_nat_eq (F := ZMod p) (p := p)
      (by omega) (by omega) (by exact_mod_cast high)
  have value : final.value = initial.value + increment := by
    unfold Word.value limbBase
    omega
  exact ⟨value, value ▸ Word.value_lt finalBounds, Word.toBitVec_add_of_value value⟩

end Airbender.Arithmetic
