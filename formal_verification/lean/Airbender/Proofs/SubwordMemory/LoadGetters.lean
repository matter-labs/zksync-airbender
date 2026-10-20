import Airbender.Proofs.SubwordMemory.LoadGeometry
import Airbender.Proofs.SubwordMemory.LoadLowSign
import Airbender.Proofs.SubwordMemory.LoadHighSign
import Airbender.Proofs.SubwordMemory.LoadRotatedByte
import Airbender.Proofs.SubwordMemory.LoadRotatedCarry
import Airbender.Proofs.Tables.PeriodicColumns
import Airbender.Proofs.Tables.BlockRanges

namespace Airbender.SubwordMemory.LoadProofs
open Setup Verification
set_option autoImplicit false

-- Copied unchanged from the checked native scalar/offset certificates.
theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

theorem affine_zero_get (length first n : Nat) (bound : n < length) :
    Block.get? (.affine length first 0) n = some (first + 0 * n) := by
  simpa only [Int.natCast_zero] using affine_get length first 0 n bound

theorem affine_one_get (length first n : Nat) (bound : n < length) :
    Block.get? (.affine length first 1) n = some (first + 1 * n) := by
  simpa only [Int.natCast_one] using affine_get length first 1 n bound

private theorem periodic_nat (values : Array Nat) (count stride n : Nat)
    (positive : 0 < values.size) (bound : n < count * values.size) :
    Block.get? (.periodic count (stride : Int) values) n =
      some (values[n % values.size]?.getD 0 + stride * (n / values.size)) := by
  have read := Setup.Proofs.periodic_get values count stride n positive bound
  simpa only [Array.getElem?_eq_getElem (Nat.mod_lt n positive), Option.getD_some] using read

theorem signed_low_get (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 0 lowSignValues) n =
      some (if n % 256 < 128 then n % 256 else n % 256 + 65280) := by
  have read := periodic_nat lowSignValues 256 0 n (by rw [lowSignValues_size]; decide)
    (by rw [lowSignValues_size]; omega)
  have sample := lowSignValues_samples ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simpa only [Int.natCast_zero, lowSignValues_size, Nat.zero_mul, Nat.add_zero, sample] using read

theorem signed_high_get (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 0 highSignValues) n =
      some (if n % 256 < 128 then 0 else 65535) := by
  have read := periodic_nat highSignValues 256 0 n (by rw [highSignValues_size]; decide)
    (by rw [highSignValues_size]; omega)
  have sample := highSignValues_samples ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simpa only [Int.natCast_zero, highSignValues_size, Nat.zero_mul, Nat.add_zero, sample] using read

theorem repeated_get (count value n : Nat) (bound : n < count * 256) :
    Block.get? (.periodic count 1 (Array.replicate 256 value)) n = some (value + n / 256) := by
  have read := periodic_nat (Array.replicate 256 value) count 1 n (by simp) (by simpa using bound)
  simpa [Nat.mod_lt n (by decide : 0 < 256)] using read

theorem range_get (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 0 (Array.range 256)) n = some (n % 256) := by
  have read := periodic_nat (Array.range 256) 256 0 n (by simp) (by simpa using bound)
  simpa [Nat.mod_lt n (by decide : 0 < 256)] using read

theorem rotated_byte_get (n : Nat) (bound : n < 65536) :
    Block.get? (.periodic 256 0 rotatedByteValues) n = some ((n + 1) % 256) := by
  have read := periodic_nat rotatedByteValues 256 0 n (by rw [rotatedByteValues_size]; decide)
    (by rw [rotatedByteValues_size]; omega)
  have sample := rotatedByteValues_samples ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simp only [Int.natCast_zero, rotatedByteValues_size, Nat.zero_mul, Nat.add_zero, sample] at read
  have same : (n % 256 + 1) % 256 = (n + 1) % 256 := by omega
  simpa only [same] using read

theorem rotated_carry_get (n : Nat) (bound : n < 65280) :
    Block.get? (.periodic 255 1 rotatedCarryValues) n = some ((n + 1) / 256) := by
  have read := periodic_nat rotatedCarryValues 255 1 n (by rw [rotatedCarryValues_size]; decide)
    (by rw [rotatedCarryValues_size]; omega)
  have sample := rotatedCarryValues_samples ⟨n % 256, Nat.mod_lt _ (by decide)⟩
  simp only [rotatedCarryValues_size, Nat.one_mul, sample] at read
  have same : (n % 256 + 1) / 256 + n / 256 = (n + 1) / 256 := by omega
  simpa only [Int.natCast_one, same] using read

theorem block_head (block : Block) (rest : List Block) (n length : Nat)
    (size : block.length = length) (bound : n < length) :
    getFromBlocks (block :: rest) n = block.get? n := by
  have selected := Setup.Proofs.selected_block [] rest block n (by rw [size]; exact bound)
  simpa only [List.nil_append, List.map_nil, List.sum_nil, Nat.zero_add] using selected

theorem block_skip (block : Block) (rest : List Block) (n length : Nat)
    (size : block.length = length) (bound : length ≤ n) :
    getFromBlocks (block :: rest) n = getFromBlocks rest (n - length) := by
  rw [getFromBlocks]
  rw [size, if_neg (by omega)]

end Airbender.SubwordMemory.LoadProofs
