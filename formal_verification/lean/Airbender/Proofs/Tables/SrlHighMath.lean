import Airbender.Review.Helpers.Tables.SrlHigh
import Airbender.Proofs.Tables.SrlLowMath

namespace Airbender.Verification.SrlHighProofs
set_option warningAsError true
set_option Elab.async false

theorem low_bound (key : Nat) : srlHighLowOutput key < 65536 := Nat.mod_lt _ (by decide)

theorem low_after_sixteen (n : Nat) :
    srlHighLowOutput (1048576 + n) = srlLowOutput n := by
  have remainder : (1048576 + n) % 65536 = n % 65536 := by omega
  have shift : (1048576 + n) / 65536 = 16 + n / 65536 := by omega
  rw [srlHighLowOutput,remainder,shift,Nat.pow_add]
  change (n % 65536 * 65536 / (65536 * 2 ^ (n / 65536))) % 65536 = _
  rw [Nat.mul_comm (n % 65536) 65536,Nat.mul_div_mul_left _ _ (by decide)]
  exact Nat.mod_eq_of_lt (SrlLowProofs.low_bound n)

theorem high_quotient (key : Nat) :
    (key % 65536 * 65536 / 2 ^ (key / 65536)) / 65536 = srlLowOutput key := by
  rw [Nat.div_div_eq_div_mul,Nat.mul_comm (2 ^ (key / 65536)) 65536,
    ← Nat.div_div_eq_div_mul,Nat.mul_div_cancel _ (by decide)]
  rfl

theorem shifted_bits (key : Nat) :
    BitVec.ofNat 32 (srlHighLowOutput key + srlLowOutput key * 65536) =
      (BitVec.ofNat 32 ((key % 65536) * 65536)) >>> (key / 65536) := by
  have low := low_bound key
  have high := SrlLowProofs.low_bound key
  have result : srlHighLowOutput key + srlLowOutput key * 65536 < 4294967296 := by omega
  have word : key % 65536 * 65536 < 4294967296 :=
    Nat.mul_lt_mul_of_pos_right (Nat.mod_lt key (by decide : 0 < 65536)) (by decide)
  have reconstruct : srlHighLowOutput key + srlLowOutput key * 65536 =
      key % 65536 * 65536 / 2 ^ (key / 65536) := by
    change (key % 65536 * 65536 / 2 ^ (key / 65536)) % 65536 + srlLowOutput key * 65536 = _
    rw [← high_quotient key]
    simpa only [Nat.mul_comm] using Nat.mod_add_div (key % 65536 * 65536 / 2 ^ (key / 65536)) 65536
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt result,BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt word,Nat.shiftRight_eq_div_pow]
  exact reconstruct

end Airbender.Verification.SrlHighProofs
