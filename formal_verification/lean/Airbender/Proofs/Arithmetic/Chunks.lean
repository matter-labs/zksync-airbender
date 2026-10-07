import Clean.Specs.BLAKE3
import Airbender.Proofs.Arithmetic.Lemmas
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Arithmetic

/-- Assemble XOR chunks without duplicating the bitwise semantics used by Clean. -/
theorem xor_of_chunks {width a₀ a₁ b₀ b₁ : Nat}
    (aBound : a₀ < 2 ^ width) (bBound : b₀ < 2 ^ width) :
    (a₀ + 2 ^ width * a₁) ^^^ (b₀ + 2 ^ width * b₁) =
      (a₀ ^^^ b₀) + 2 ^ width * (a₁ ^^^ b₁) := by
  rw [xor_eq_add width aBound, xor_eq_add width bBound,
    xor_eq_add width (Nat.xor_lt_two_pow aBound bBound), xor_mul_two_pow]
  ac_rfl

/-- Clean's rotation moves the low chunk to the top and the high chunk to the bottom. -/
theorem rotate_right_of_chunks {width low high : Nat} (widthBound : width < 32)
    (lowBound : low < 2 ^ width) :
    rotRight32 (low + 2 ^ width * high) width = low * 2 ^ (32 - width) + high := by
  simp [rotRight32, Nat.mod_eq_of_lt widthBound, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left, Nat.mod_eq_of_lt lowBound, Nat.div_eq_of_lt lowBound]

/-- A bounded scaled remainder reconstructs the canonical field value. Chunk
    widths may differ; the combined range must fit below the characteristic. -/
theorem value_of_scaled_chunks {p radix capacity : Nat} [Fact p.Prime]
    (hp : radix * capacity ≤ p) {x low inverse : ZMod p}
    (compatible : (radix : ZMod p) * inverse = 1)
    (lowBound : low.val < radix) (highBound : (inverse * (x - low)).val < capacity) :
    x.val = low.val + radix * (inverse * (x - low)).val := by
  have small : low.val + radix * (inverse * (x - low)).val < p := by
    calc
      _ < radix + radix * (inverse * (x - low)).val := Nat.add_lt_add_right lowBound _
      _ = radix * ((inverse * (x - low)).val + 1) := by ring
      _ ≤ radix * capacity := Nat.mul_le_mul_left _ (by omega)
      _ ≤ p := hp
  have field : ((low.val + radix * (inverse * (x - low)).val : Nat) : ZMod p) = x := by
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
    linear_combination (x - low) * compatible
  calc
    x.val = (((low.val + radix * (inverse * (x - low)).val : Nat) : ZMod p)).val :=
      congrArg ZMod.val field.symm
    _ = _ := ZMod.val_natCast_of_lt small

/-- Two carry bits initially encode 0..3. The bounded limb equations exclude 3
    before reusing the shared addition proof and Clean's modular addition. -/
theorem Word.add32_of_limbs {p : Nat} [Fact p.Prime] (hp : 262144 ≤ p)
    {left right message output : Word} {carry wrap : Nat}
    (leftBound : left.Bounded) (rightBound : right.Bounded)
    (messageBound : message.Bounded) (outputBound : output.Bounded)
    (carryBound : carry ≤ 3) (wrapBound : wrap ≤ 3)
    (low : (left.lo : ZMod p) + right.lo + message.lo = output.lo + 65536 * carry)
    (high : (carry : ZMod p) + left.hi + right.hi + message.hi = output.hi + 65536 * wrap) :
    output.value = add32 left.value (add32 right.value message.value) := by
  have ll := leftBound.1; have lh := leftBound.2
  have rl := rightBound.1; have rh := rightBound.2
  have ml := messageBound.1; have mh := messageBound.2
  have ol := outputBound.1; have oh := outputBound.2
  unfold limbBase at ll lh rl rh ml mh ol oh
  have lowNat : left.lo + right.lo + message.lo = output.lo + 65536 * carry :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast low)
  have cb : carry ≤ 2 := by omega
  have highNat : carry + left.hi + right.hi + message.hi = output.hi + 65536 * wrap :=
    bounded_nat_eq (F := ZMod p) (p := p) (by omega) (by omega) (by exact_mod_cast high)
  have wb : wrap ≤ 2 := by omega
  have words := Word.add_of_limbs (by omega) leftBound rightBound messageBound outputBound cb wb low high
  have values := congrArg BitVec.toNat words
  simp only [BitVec.toNat_add, Word.toBitVec_toNat leftBound,
    Word.toBitVec_toNat rightBound, Word.toBitVec_toNat messageBound,
    Word.toBitVec_toNat outputBound] at values
  simpa [add32, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc] using values

end Airbender.Arithmetic
