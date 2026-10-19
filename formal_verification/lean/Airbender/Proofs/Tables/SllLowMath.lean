import Airbender.Review.Helpers.Tables.SllLow

namespace Airbender.Verification.SllLowProofs
set_option warningAsError true
set_option Elab.async false

theorem high_bound (key : Nat) : sllLowHighOutput key < 65536 := Nat.mod_lt _ (by decide)

theorem high_after_sixteen (n : Nat) :
    sllLowHighOutput (1048576 + n) = sllHighOutput n := by
  have remainder : (1048576 + n) % 65536 = n % 65536 := by omega
  have shift : (1048576 + n) / 65536 = 16 + n / 65536 := by omega
  rw [sllLowHighOutput,remainder,shift,Nat.pow_add]
  change (n % 65536 * (65536 * 2 ^ (n / 65536)) / 65536) % 65536 = _
  rw [Nat.mul_left_comm (n % 65536) 65536, Nat.mul_div_cancel_left _ (by decide)]
  rfl

theorem shifted_bits (key : Nat) :
    BitVec.ofNat 32 (sllHighOutput key + sllLowHighOutput key * 65536) =
      (BitVec.ofNat 32 (key % 65536)) <<< (key / 65536) := by
  have low : sllHighOutput key < 65536 := Nat.mod_lt _ (by decide)
  have high := high_bound key
  have result : sllHighOutput key + sllLowHighOutput key * 65536 < 4294967296 := by omega
  have word : key % 65536 < 4294967296 := by have := Nat.mod_lt key (by decide : 0 < 65536); omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt result,BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt word,Nat.shiftLeft_eq]
  change sllHighOutput key + sllLowHighOutput key * 65536 =
    (key % 65536 * 2 ^ (key / 65536)) % (65536 * 65536)
  rw [Nat.mod_mul]
  exact congrArg (fun high => sllHighOutput key + high) (Nat.mul_comm _ _)

end Airbender.Verification.SllLowProofs
