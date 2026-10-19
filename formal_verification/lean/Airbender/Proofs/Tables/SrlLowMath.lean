import Airbender.Review.Helpers.Tables.SrlLow

namespace Airbender.Verification.SrlLowProofs
set_option warningAsError true
set_option Elab.async false

theorem low_bound (key : Nat) : srlLowOutput key < 65536 := by
  have word : key % 65536 < 65536 := Nat.mod_lt _ (by decide)
  have divided := Nat.div_le_self (key % 65536) (2 ^ (key / 65536))
  exact lt_of_le_of_lt divided word

theorem low_bits (key : Nat) : BitVec.ofNat 32 (srlLowOutput key) =
    (BitVec.ofNat 32 (key % 65536)) >>> (key / 65536) := by
  have word : key % 65536 < 4294967296 := by have := Nat.mod_lt key (by decide : 0 < 65536); omega
  have result : srlLowOutput key < 4294967296 := by have := low_bound key; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt result,BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt word,Nat.shiftRight_eq_div_pow]
  rfl

end Airbender.Verification.SrlLowProofs
