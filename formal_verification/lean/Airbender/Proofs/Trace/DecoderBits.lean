import Airbender.Review.Properties
import Mathlib.Tactic.FinCases

namespace Airbender.Trace.Proofs

/-- Boolean selector packing is injective below the field modulus. The nine-bit
    width comes from the imported ADD/SUB descriptor; this lemma has no ISA spec. -/
theorem unpack_decoder_bits {p : Nat} [Fact p.Prime] (hp : 512 < p)
    {bits : Fin 9 → ZMod p} {mask : Nat} (small : mask < 512)
    (boolean : ∀ i, bits i = 0 ∨ bits i = 1)
    (packed : (∑ i : Fin 9, (2 ^ i.val : Nat) * bits i) = (mask : ZMod p)) :
    ∀ i, bits i = if mask.testBit i.val then 1 else 0 := by
  have oneval : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (by omega : 1 < p))
  have bound : ∀ i, (bits i).val ≤ 1 := by
    intro i
    rcases boolean i with zero | one
    · simp [zero]
    · simp [one, oneval]
  have totalBound : (∑ i : Fin 9, 2 ^ i.val * (bits i).val) ≤ 511 := by
    calc
      _ ≤ ∑ i : Fin 9, 2 ^ i.val * 1 :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (bound i)
      _ = 511 := by decide
  have cast : ((∑ i : Fin 9, 2 ^ i.val * (bits i).val : Nat) : ZMod p) = mask := by
    simpa only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val] using packed
  have total := congrArg ZMod.val cast
  rw [ZMod.val_natCast_of_lt (by omega : (∑ i : Fin 9, 2 ^ i.val * (bits i).val) < p),
    ZMod.val_natCast_of_lt (by omega : mask < p)] at total
  let value (index : Nat) := (bits (Fin.ofNat 9 index)).val
  have b0 : value 0 ≤ 1 := bound 0
  have b1 : value 1 ≤ 1 := bound 1
  have b2 : value 2 ≤ 1 := bound 2
  have b3 : value 3 ≤ 1 := bound 3
  have b4 : value 4 ≤ 1 := bound 4
  have b5 : value 5 ≤ 1 := bound 5
  have b6 : value 6 ≤ 1 := bound 6
  have b7 : value 7 ≤ 1 := bound 7
  have b8 : value 8 ≤ 1 := bound 8
  norm_num [Fin.sum_univ_succ] at total
  change value 0 + (2 * value 1 + (4 * value 2 + (8 * value 3 + (16 * value 4 +
    (32 * value 5 + (64 * value 6 + (128 * value 7 + 256 * value 8))))))) = mask at total
  intro i
  apply ZMod.val_injective
  have index : Fin.ofNat 9 i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  conv_lhs => rw [← index]
  change value i.val = (if mask.testBit i.val then (1 : ZMod p) else 0).val
  fin_cases i
  all_goals conv_rhs => simp [Nat.testBit, Nat.shiftRight_eq_div_pow, oneval]
  all_goals split_ifs
  all_goals simp only [ZMod.val_zero, oneval]
  all_goals omega

end Airbender.Trace.Proofs
