import Airbender.Proofs.Tables.LoadByteTemplates
import Airbender.Proofs.Tables.LoadByteMeaning
import Airbender.Proofs.Tables.BlockRanges

namespace Airbender.Verification.SubwordFixed
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem byte_negative_ranges (n : Nat) (bound : n < 262144) :
    byteNegative n ↔
      (65536 ≤ n ∧ n < 131072 ∧ 128 ≤ n % 256) ∨ 229376 ≤ n := by
  unfold byteNegative byteValue
  split_ifs <;> omega

private theorem constant_block (length value n : Nat) (bound : n < length) :
    Block.get? (.affine length value 0) n = some value := by
  simp [Block.get?, Block.length, bound]

private theorem signed_high_get (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 0 highSignValues) n =
      some (if n % 256 < 128 then 65535 else 0) := by
  have extent : n < 256 * highSignValues.size := by rw [highSign_size]; omega
  have positive : 0 < highSignValues.size := by rw [highSign_size]; decide
  have row := periodic_get highSignValues 256 0 n positive extent
  have sample := highSign_samples ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simpa only [Int.natCast_zero, highSign_size, Nat.zero_mul, Nat.add_zero, sample] using row

/-- Imported high output, including the native periodic block crossing a mode boundary. -/
theorem loadByte_high (n : Nat) (bound : n < 262144) :
    loadByteData.columns[2].get? n = some (byteHigh n) := by
  let b0 := Block.affine 65664 0 0
  let b1 := Block.periodic 256 0 highSignValues
  let b2 := Block.affine 98176 0 0
  let b3 := Block.affine 32768 65535 0
  rw [byte_high_shape]
  change getFromBlocks [b0, b1, b2, b3] n = some (byteHigh n)
  by_cases first : n < 65664
  · have select := selected_at [] [b1, b2, b3] b0 0 n (by simp) (by omega)
      (by simpa [b0, Block.length] using first)
    simp only [List.nil_append] at select
    rw [select]
    have sign : ¬ byteNegative n := by rw [byte_negative_ranges n bound]; omega
    simpa only [b0, Nat.sub_zero, byteHigh, if_neg sign] using constant_block 65664 0 n first
  · by_cases second : n < 131200
    · have extent : n - 65664 < 65536 := by omega
      have select := selected_at [b0] [b2, b3] b1 65664 n
        (by simp [b0, Block.length]) (by omega)
        (by simpa [b1, Block.length, highSign_size] using extent)
      simp only [List.nil_append, List.cons_append] at select
      rw [select]
      have pattern : byteNegative n ↔ (n - 65664) % 256 < 128 := by
        rw [byte_negative_ranges n bound]
        omega
      have meaning : byteHigh n = if (n - 65664) % 256 < 128 then 65535 else 0 := by
        simp only [byteHigh, pattern]
      simpa only [b1, meaning] using signed_high_get (n - 65664) extent
    · by_cases third : n < 229376
      · have extent : n - 131200 < 98176 := by omega
        have select := selected_at [b0, b1] [b3] b2 131200 n
          (by simp [b0, b1, Block.length, highSign_size]) (by omega)
          (by simpa [b2, Block.length] using extent)
        simp only [List.nil_append, List.cons_append] at select
        rw [select]
        have sign : ¬ byteNegative n := by rw [byte_negative_ranges n bound]; omega
        simpa only [b2, byteHigh, if_neg sign] using constant_block 98176 0 (n - 131200) extent
      · have extent : n - 229376 < 32768 := by omega
        have select := selected_at [b0, b1, b2] [] b3 229376 n
          (by simp [b0, b1, b2, Block.length, highSign_size]) (by omega)
          (by simpa [b3, Block.length] using extent)
        simp only [List.nil_append, List.cons_append] at select
        rw [select]
        have sign : byteNegative n := by rw [byte_negative_ranges n bound]; omega
        simpa only [b3, byteHigh, if_pos sign] using constant_block 32768 65535 (n - 229376) extent

end Airbender.Verification.SubwordFixed
