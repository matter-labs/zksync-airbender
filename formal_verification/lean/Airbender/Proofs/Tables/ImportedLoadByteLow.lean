import Airbender.Proofs.Tables.LoadByteTemplates
import Airbender.Proofs.Tables.LoadByteMeaning
import Airbender.Proofs.Tables.ImportedStorePlace
import Airbender.Proofs.Tables.BlockRanges

namespace Airbender.Verification.SubwordFixed
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem signed_low_get (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 0 lowSignValues) n =
      some (if n % 256 < 128 then n % 256 else n % 256 + 65280) := by
  have extent : n < 256 * lowSignValues.size := by rw [lowSign_size]; omega
  have positive : 0 < lowSignValues.size := by rw [lowSign_size]; decide
  have row := periodic_get lowSignValues 256 0 n positive extent
  have sample := lowSign_samples ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simpa only [Int.natCast_zero, lowSign_size, Nat.zero_mul, Nat.add_zero, sample] using row

private theorem repeated_value (count first n : Nat) (bound : n < count * 256) :
    Block.get? (.periodic count 1 (Array.replicate 256 first)) n =
      some (first + n / 256) := by
  have row := periodic_get (Array.replicate 256 first) count 1 n (by simp)
    (by simpa only [Array.size_replicate] using bound)
  simpa using row

/-- Imported low output for all four byte-load control combinations. -/
theorem loadByte_low (n : Nat) (bound : n < 262144) :
    loadByteData.columns[1].get? n = some (byteLow n) := by
  let b0 := Block.periodic 256 0 (Array.range 256)
  let b1 := Block.periodic 256 0 lowSignValues
  let b2 := Block.periodic 256 1 (Array.replicate 256 0)
  let b3 := Block.periodic 128 1 (Array.replicate 256 0)
  let b4 := Block.periodic 128 1 (Array.replicate 256 65408)
  rw [byte_low_shape]
  change getFromBlocks [b0, b1, b2, b3, b4] n = some (byteLow n)
  by_cases first : n < 65536
  · have select := selected_at [] [b1, b2, b3, b4] b0 0 n (by simp) (by omega)
      (by simpa [b0, Block.length] using first)
    simp only [List.nil_append] at select
    rw [select]
    have row := periodic_range 256 n first
    have low : n < 131072 := by omega
    have flag : n / 65536 % 2 = 0 := by omega
    simpa [b0, byteLow, byteNegative, byteValue, low, flag] using row
  · by_cases second : n < 131072
    · have extent : n - 65536 < 65536 := by omega
      have select := selected_at [b0] [b2, b3, b4] b1 65536 n
        (by simp [b0, Block.length]) (by omega)
        (by simpa [b1, Block.length, lowSign_size] using extent)
      simp only [List.nil_append, List.cons_append] at select
      rw [select]
      have residue : (n - 65536) % 256 = n % 256 := by omega
      have flag : n / 65536 % 2 = 1 := by omega
      have meaning : byteLow n = if n % 256 < 128 then n % 256 else n % 256 + 65280 := by
        by_cases sign : n % 256 < 128
        · have positive : ¬ 128 ≤ n % 256 := by omega
          simp [byteLow, byteNegative, byteValue, second, flag, sign, positive]
        · have negative : 128 ≤ n % 256 := by omega
          simp [byteLow, byteNegative, byteValue, second, flag, sign, negative]
      simpa only [b1, residue, meaning] using signed_low_get (n - 65536) extent
    · by_cases third : n < 196608
      · have extent : n - 131072 < 65536 := by omega
        have select := selected_at [b0, b1] [b3, b4] b2 131072 n
          (by simp [b0, b1, Block.length, lowSign_size]) (by omega)
          (by simpa [b2, Block.length] using extent)
        simp only [List.nil_append, List.cons_append] at select
        rw [select]
        have flag : n / 65536 % 2 = 0 := by omega
        have value : (n - 131072) / 256 = n / 256 % 256 := by omega
        have row := repeated_value 256 0 (n - 131072) extent
        simpa [b2, byteLow, byteNegative, byteValue, second, flag, value] using row
      · by_cases fourth : n < 229376
        · have extent : n - 196608 < 32768 := by omega
          have select := selected_at [b0, b1, b2] [b4] b3 196608 n
            (by simp [b0, b1, b2, Block.length, lowSign_size]) (by omega)
            (by simpa [b3, Block.length] using extent)
          simp only [List.nil_append, List.cons_append] at select
          rw [select]
          have flag : n / 65536 % 2 = 1 := by omega
          have value : (n - 196608) / 256 = n / 256 % 256 := by omega
          have positive : ¬ 128 ≤ n / 256 % 256 := by omega
          have row := repeated_value 128 0 (n - 196608) extent
          simpa [b3, byteLow, byteNegative, byteValue, second, flag, value, positive] using row
        · have extent : n - 229376 < 32768 := by omega
          have select := selected_at [b0, b1, b2, b3] [] b4 229376 n
            (by simp [b0, b1, b2, b3, Block.length, lowSign_size]) (by omega)
            (by simpa [b4, Block.length] using extent)
          simp only [List.nil_append, List.cons_append] at select
          rw [select]
          have flag : n / 65536 % 2 = 1 := by omega
          have value : 65408 + (n - 229376) / 256 = n / 256 % 256 + 65280 := by omega
          have negative : 128 ≤ n / 256 % 256 := by omega
          have row := repeated_value 128 65408 (n - 229376) extent
          simpa [b4, byteLow, byteNegative, byteValue, second, flag, value, negative] using row

end Airbender.Verification.SubwordFixed
