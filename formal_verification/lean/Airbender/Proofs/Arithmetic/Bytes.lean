import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Arithmetic

/-- Reassemble four native bytes. Shared by byte-oriented circuit families. -/
theorem bytes_value (x : BitVec 32) :
    x.toNat = (x.extractLsb' 0 8).toNat + 256 * (x.extractLsb' 8 8).toNat +
      65536 * (x.extractLsb' 16 8).toNat + 16777216 * (x.extractLsb' 24 8).toNat := by
  have bound := x.isLt
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  norm_num only [Nat.reducePow, Nat.div_one] at *
  omega

end Airbender.Arithmetic
