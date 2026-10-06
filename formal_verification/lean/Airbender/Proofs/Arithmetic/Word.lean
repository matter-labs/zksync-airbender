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

/-- Addition with a low carry and a high wrap carry, reusable across circuit families. -/
theorem Word.add_of_limbs {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {left right immediate output : Word} {carry wrap : Nat}
    (leftBound : left.Bounded) (rightBound : right.Bounded)
    (immediateBound : immediate.Bounded) (outputBound : output.Bounded)
    (carryBound : carry ≤ 1) (wrapBound : wrap ≤ 1)
    (low : (left.lo : ZMod p) + right.lo + immediate.lo = output.lo + 65536 * carry)
    (high : (carry : ZMod p) + left.hi + right.hi + immediate.hi = output.hi + 65536 * wrap) :
    output.toBitVec = left.toBitVec + right.toBitVec + immediate.toBitVec := by
  have al := leftBound.1; have ah := leftBound.2
  have bl := rightBound.1; have bh := rightBound.2
  have ml := immediateBound.1; have mh := immediateBound.2
  have rl := outputBound.1; have rh := outputBound.2
  unfold limbBase at al ah bl bh ml mh rl rh
  have lowNat : left.lo + right.lo + immediate.lo = output.lo + 65536 * carry :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast low)
  have highNat : carry + left.hi + right.hi + immediate.hi = output.hi + 65536 * wrap :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast high)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, Word.toBitVec_toNat leftBound,
    Word.toBitVec_toNat rightBound, Word.toBitVec_toNat immediateBound,
    Word.toBitVec_toNat outputBound, Word.value, limbBase]
  omega

/-- Subtraction with two borrow bits, reusable across circuit families. -/
theorem Word.sub_of_limbs {p : Nat} [Fact p.Prime] (hp : 131072 < p)
    {left right output : Word} {borrow wrap : Nat}
    (leftBound : left.Bounded) (rightBound : right.Bounded) (outputBound : output.Bounded)
    (borrowBound : borrow ≤ 1) (wrapBound : wrap ≤ 1)
    (low : (output.lo : ZMod p) + right.lo = left.lo + 65536 * borrow)
    (high : (borrow : ZMod p) + output.hi + right.hi = left.hi + 65536 * wrap) :
    output.toBitVec = left.toBitVec - right.toBitVec := by
  have al := leftBound.1; have ah := leftBound.2
  have bl := rightBound.1; have bh := rightBound.2
  have rl := outputBound.1; have rh := outputBound.2
  unfold limbBase at al ah bl bh rl rh
  have lowNat : output.lo + right.lo = left.lo + 65536 * borrow :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast low)
  have highNat : borrow + output.hi + right.hi = left.hi + 65536 * wrap :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast high)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, Word.toBitVec_toNat leftBound,
    Word.toBitVec_toNat rightBound, Word.toBitVec_toNat outputBound, Word.value, limbBase]
  omega

/-- A forced final subtraction borrow proves a strict comparison. The comparison
    remainder is range checked; its value is not supplied as a desired inequality. -/
theorem Word.lt_of_borrow {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {output modulus remainder : Word} {carry : Nat}
    (outputBound : output.Bounded) (modulusBound : modulus.Bounded)
    (remainderBound : remainder.Bounded) (carryBound : carry ≤ 1)
    (low : (remainder.lo : ZMod p) + modulus.lo = output.lo + 65536 * carry)
    (high : (carry : ZMod p) + remainder.hi + modulus.hi = output.hi + 65536) :
    output.value < modulus.value := by
  have ol := outputBound.1; have oh := outputBound.2
  have ml := modulusBound.1; have mh := modulusBound.2
  have rl := remainderBound.1; have rh := remainderBound.2
  unfold limbBase at ol oh ml mh rl rh
  have lowNat : remainder.lo + modulus.lo = output.lo + 65536 * carry :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast low)
  have highNat : carry + remainder.hi + modulus.hi = output.hi + 65536 :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast high)
  unfold Word.value limbBase
  omega

end Airbender.Arithmetic
