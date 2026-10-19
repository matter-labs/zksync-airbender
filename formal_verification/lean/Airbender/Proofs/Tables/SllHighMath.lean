import Airbender.Review.Helpers.Tables.SllHigh

namespace Airbender.Verification.SllHighProofs
set_option warningAsError true
set_option Elab.async false

theorem high_bound (key : Nat) : sllHighOutput key < 65536 := Nat.mod_lt _ (by decide)

theorem high_bits (key : Nat) : BitVec.ofNat 32 (sllHighOutput key * 65536) =
    (BitVec.ofNat 32 ((key % 65536) * 65536)) <<< (key / 65536) := by
  have word : key % 65536 * 65536 < 4294967296 :=
    Nat.mul_lt_mul_of_pos_right (Nat.mod_lt key (by decide : 0 < 65536)) (by decide)
  have result : sllHighOutput key * 65536 < 4294967296 :=
    Nat.mul_lt_mul_of_pos_right (high_bound key) (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt result,BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt word,Nat.shiftLeft_eq]
  change sllHighOutput key * 65536 =
    ((key % 65536) * 65536 * 2 ^ (key / 65536)) % (65536 * 65536)
  rw [Nat.mul_right_comm (key % 65536) 65536 (2 ^ (key / 65536)),Nat.mul_mod_mul_right]
  rfl

end Airbender.Verification.SllHighProofs
