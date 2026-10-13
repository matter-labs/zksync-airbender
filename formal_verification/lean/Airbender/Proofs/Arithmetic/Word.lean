import Airbender.Review.Helpers.Word
import Airbender.Proofs.Arithmetic.Lemmas
import Mathlib.Data.Nat.Basic

namespace Airbender.Arithmetic

theorem Word.ofBitVec_bound (bits : BitVec 32) : (Word.ofBitVec bits).Bounded := by
  constructor
  · exact Nat.mod_lt _ (by decide)
  · have bound := bits.isLt
    change bits.toNat / limbBase < limbBase
    apply (Nat.div_lt_iff_lt_mul (by decide : 0 < limbBase)).mpr
    simpa [limbBase] using bound

theorem Word.ofBitVec_value (bits : BitVec 32) : (Word.ofBitVec bits).value = bits.toNat := by
  exact Nat.mod_add_div _ _

theorem Word.eq_of_value {left right : Word} (leftBound : left.Bounded)
    (rightBound : right.Bounded) (equal : left.value = right.value) : left = right := by
  have low : left.lo = right.lo := by
    dsimp [Word.value, Word.Bounded, limbBase] at equal leftBound rightBound
    omega
  have high : left.hi = right.hi := by
    dsimp [Word.value, limbBase] at equal
    omega
  cases left
  cases right
  simp_all

theorem Word.ofBitVec_roundtrip (bits : BitVec 32) : (Word.ofBitVec bits).toBitVec = bits := by
  simp [Word.toBitVec, Word.ofBitVec_value]

/-- Native word masking removes exactly the least significant bit. -/
theorem clear_low_bit_toNat (x : BitVec 32) :
    (x &&& 0xfffffffe).toNat = x.toNat - x.toNat % 2 := by
  change (x &&& BitVec.ofNat 32 4294967294).toNat = _
  have mask := BitVec.shiftLeft_ushiftRight (x := x) (n := 1)
  change (x >>> 1) <<< 1 = x &&& BitVec.ofNat 32 4294967294 at mask
  rw [← mask, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have bound := x.isLt
  norm_num only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem Word.value_lt {word : Word} (h : word.Bounded) : word.value < wordModulus := by
  rcases h with ⟨hl, hh⟩
  unfold Word.value limbBase wordModulus at *
  omega

@[simp] theorem Word.toBitVec_toNat {word : Word} (h : word.Bounded) :
    word.toBitVec.toNat = word.value :=
  Nat.mod_eq_of_lt (Word.value_lt h)

theorem Word.eq_zero_of_bounded {word : Word} (bounded : word.Bounded)
    (zero : word.toBitVec = 0) : word = ⟨0, 0⟩ := by
  have value := congrArg BitVec.toNat zero
  rw [Word.toBitVec_toNat bounded] at value
  change word.lo + limbBase * word.hi = 0 at value
  have low : word.lo = 0 := by omega
  have high : word.hi = 0 := by dsimp [limbBase] at value; omega
  cases word
  simp_all

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
    (carryBound : carry ≤ 2) (wrapBound : wrap ≤ 2)
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

/-- A range-checked subtraction remainder makes the final borrow exactly the
    unsigned comparison. Shared by modular reduction and comparison circuits. -/
theorem Word.borrow_iff {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {left right remainder : Word} {carry borrow : Nat}
    (leftBound : left.Bounded) (rightBound : right.Bounded)
    (remainderBound : remainder.Bounded) (carryBound : carry ≤ 1) (borrowBound : borrow ≤ 1)
    (low : (remainder.lo : ZMod p) + right.lo = left.lo + 65536 * carry)
    (high : (carry : ZMod p) + remainder.hi + right.hi = left.hi + 65536 * borrow) :
    borrow = 1 ↔ left.value < right.value := by
  have ll := leftBound.1; have lh := leftBound.2
  have rl := rightBound.1; have rh := rightBound.2
  have ml := remainderBound.1; have mh := remainderBound.2
  unfold limbBase at ll lh rl rh ml mh
  have lowNat : remainder.lo + right.lo = left.lo + 65536 * carry :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast low)
  have highNat : carry + remainder.hi + right.hi = left.hi + 65536 * borrow :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast high)
  unfold Word.value limbBase
  omega

/-- A forced final subtraction borrow proves strict comparison. -/
theorem Word.lt_of_borrow {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {output modulus remainder : Word} {carry : Nat}
    (outputBound : output.Bounded) (modulusBound : modulus.Bounded)
    (remainderBound : remainder.Bounded) (carryBound : carry ≤ 1)
    (low : (remainder.lo : ZMod p) + modulus.lo = output.lo + 65536 * carry)
    (high : (carry : ZMod p) + remainder.hi + modulus.hi = output.hi + 65536) :
    output.value < modulus.value :=
  (Word.borrow_iff hp outputBound modulusBound remainderBound carryBound (borrow := 1)
    (by decide) low (by simpa using high)).mp rfl

end Airbender.Arithmetic
