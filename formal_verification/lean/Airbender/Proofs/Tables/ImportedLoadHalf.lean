import Airbender.Data.Tables.Subword.LoadHalfData
import Airbender.Proofs.Tables.ImportedStorePlace

namespace Airbender.Verification.SubwordFixed
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem half_low_shape : loadHalfData.columns[1] = Column.mk
    #[.periodic 1 0 (Array.range 256), .affine 65280 256 1,
      .affine 65536 0 1] := rfl
private theorem half_high_shape : loadHalfData.columns[2] = Column.mk
    #[.affine 98304 0 0, .affine 32768 65535 0] := rfl

private theorem unit_get (length first n : Nat) (bound : n < length) :
    Block.get? (.affine length first 1) n = some (first + n) := by
  simp [Block.get?, Block.length, bound]
  simpa only [Int.natCast_add] using
    And.intro (Int.natCast_nonneg (first + n)) (Int.toNat_natCast (first + n))

private theorem half_meaning (n : Nat) (bound : n < 131072) :
    subwordLoadLimbs false n =
      (n % 65536, if 98304 ≤ n then 65535 else 0) := by
  have sign : (n / 65536 % 2 = 1 ∧ 32768 ≤ n % 65536) ↔ 98304 ≤ n := by omega
  change (n % 65536, if n / 65536 % 2 = 1 ∧ 32768 ≤ n % 65536 then 65535 else 0) = _
  simp only [sign]

private theorem half_low (n : Nat) (bound : n < 131072) :
    loadHalfData.columns[1].get? n = some (n % 65536) := by
  rw [half_low_shape]
  by_cases first : n < 256
  · simp only [Column.get?, getFromBlocks, Block.length, Array.size_range,
      Nat.one_mul, if_pos first]
    have value : n % 65536 = n % 256 := by omega
    rw [value]
    exact periodic_range 1 n (by omega)
  · by_cases second : n < 65536
    · have extent : n - 256 < 65280 := by omega
      simp only [Column.get?, getFromBlocks, Block.length, Array.size_range,
        Nat.one_mul, if_neg first, if_pos extent]
      have value : 256 + (n - 256) = n % 65536 := by omega
      exact (unit_get 65280 256 (n - 256) extent).trans (congrArg some value)
    · have outside : ¬ n - 256 < 65280 := by omega
      have extent : n - 256 - 65280 < 65536 := by omega
      simp only [Column.get?, getFromBlocks, Block.length, Array.size_range,
        Nat.one_mul, if_neg first, if_neg outside, if_pos extent]
      have value : 0 + (n - 256 - 65280) = n % 65536 := by omega
      exact (unit_get 65536 0 (n - 256 - 65280) extent).trans (congrArg some value)

private theorem constant_get (length value n : Nat) (bound : n < length) :
    Block.get? (.affine length value 0) n = some value := by
  simp [Block.get?, Block.length, bound]

private theorem half_high (n : Nat) (bound : n < 131072) :
    loadHalfData.columns[2].get? n = some (if 98304 ≤ n then 65535 else 0) := by
  rw [half_high_shape]
  by_cases first : n < 98304
  · have sign : ¬ 98304 ≤ n := by omega
    simp only [Column.get?, getFromBlocks, Block.length, if_pos first, if_neg sign]
    exact constant_get 98304 0 n first
  · have extent : n - 98304 < 32768 := by omega
    have sign : 98304 ≤ n := by omega
    simp only [Column.get?, getFromBlocks, Block.length, if_neg first, if_pos extent, if_pos sign]
    exact constant_get 32768 65535 (n - 98304) extent

/-- Every imported halfword-load output, including the sign boundary. -/
theorem loadHalf_outputs (n : Nat) (bound : n < 131072) :
    loadHalfData.columns[1].get? n = some (subwordLoadLimbs false n).1 ∧
      loadHalfData.columns[2].get? n = some (subwordLoadLimbs false n).2 := by
  rw [half_meaning n bound]
  exact ⟨half_low n bound, half_high n bound⟩

end Airbender.Verification.SubwordFixed
