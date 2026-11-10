import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Properties
import Clean.Utils.Bits
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace Airbender.Trace.Proofs

theorem unpack_decoder_bits_general {p n : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p (2 ^ n))
    {bits : Fin n → ZMod p} {mask : Nat} (small : mask < 2 ^ n)
    (boolean : ∀ i, bits i = 0 ∨ bits i = 1)
    (packed : (∑ i : Fin n, (2 ^ i.val : Nat) * bits i) = (mask : ZMod p)) :
    ∀ i, bits i = if mask.testBit i.val then 1 else 0 := by
  let vector : Vector (ZMod p) n := Vector.ofFn bits
  have flags : ∀ i (hi : i < n), vector[i] = 0 ∨ vector[i] = 1 := by
    intro i hi
    simpa [vector] using boolean ⟨i, hi⟩
  have field : Utils.Bits.fieldFromBits vector = (mask : ZMod p) := by
    simpa [Utils.Bits.fieldFromBits, Utils.Bits.fromBits, Fin.foldl_to_sum,
      vector, Nat.cast_sum, Nat.cast_mul, mul_comm] using packed
  have inverse := Utils.Bits.fieldToBits_fieldFromBits hp vector flags
  rw [field] at inverse
  intro i
  have bit := congrArg (fun v : Vector (ZMod p) n => v[i]) inverse
  simpa [Utils.Bits.fieldToBits, Utils.Bits.toBits, vector,
    Fin.getElem_fin, Vector.getElem_mapRange,
    ZMod.val_natCast_of_lt (small.trans hp)] using bit.symm

theorem unpack_decoder_bits {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 512)
    {bits : Fin 9 → ZMod p} {mask : Nat} (small : mask < 512)
    (boolean : ∀ i, bits i = 0 ∨ bits i = 1)
    (packed : (∑ i : Fin 9, (2 ^ i.val : Nat) * bits i) = (mask : ZMod p)) :
    ∀ i, bits i = if mask.testBit i.val then 1 else 0 :=
  unpack_decoder_bits_general (by simpa using hp) (by simpa using small) boolean packed

/-- Narrower families reuse the same packing proof by padding unused bits with
    zero. No enumeration of instruction masks is needed. -/
theorem unpack_decoder_bits_of_width {p n : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 512)
    (width : n ≤ 9) {bits : Fin n → ZMod p} {mask : Nat} (small : mask < 512)
    (boolean : ∀ i, bits i = 0 ∨ bits i = 1)
    (packed : (∑ i : Fin n, (2 ^ i.val : Nat) * bits i) = (mask : ZMod p)) :
    ∀ i, bits i = if mask.testBit i.val then 1 else 0 := by
  let padded (i : Fin 9) : ZMod p := if h : i.val < n then bits ⟨i.val, h⟩ else 0
  have padBoolean : ∀ i, padded i = 0 ∨ padded i = 1 := by
    intro i
    dsimp [padded]
    split
    · exact boolean _
    · exact Or.inl rfl
  have sameSum : (∑ i : Fin 9, (2 ^ i.val : Nat) * padded i) =
      ∑ i : Fin n, (2 ^ i.val : Nat) * bits i := by
    interval_cases n <;> simp [padded, Fin.sum_univ_succ]
  have unpacked := unpack_decoder_bits hp small padBoolean (sameSum.trans packed)
  intro i
  have bit := unpacked ⟨i.val, by omega⟩
  simpa [padded, i.isLt] using bit

end Airbender.Trace.Proofs
