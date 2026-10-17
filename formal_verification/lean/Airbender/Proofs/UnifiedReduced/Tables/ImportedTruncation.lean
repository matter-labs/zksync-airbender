import Airbender.Review.Circuits.UnifiedReduced.Tables.Native.TruncationData
import Airbender.Proofs.Tables.PeriodicColumns
import Airbender.Proofs.Tables.BlockRanges
import Airbender.Proofs.Tables.ShiftKeys

namespace Airbender.UnifiedReduced.Setup.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private theorem repeated_value (count first n : Nat) (bound : n < count * 256) :
    Block.get? (.periodic count 1 (Array.replicate 256 first)) n = some (first + n / 256) := by
  have row := periodic_get (Array.replicate 256 first) count 1 n (by simp)
    (by simpa only [Array.size_replicate] using bound)
  simpa using row

private theorem truncation_shape : nativeTruncationData.columns[2] = Column.mk
    #[.affine 256 0 0, .periodic 31 1 (Array.replicate 256 1),
      .periodic 32 1 (Array.replicate 256 0), .periodic 32 1 (Array.replicate 256 0),
      .periodic 32 1 (Array.replicate 256 0), .periodic 32 1 (Array.replicate 256 0),
      .periodic 32 1 (Array.replicate 256 0), .periodic 32 1 (Array.replicate 256 0),
      .periodic 32 1 (Array.replicate 256 0)] := rfl

/-- The native first group is split at byte zero; all eight groups retain low five bits. -/
theorem imported_truncation_output (n : Nat) (bound : n < 65536) :
    nativeTruncationData.columns[2].get? n = some (n / 256 % 32) := by
  let first := Block.affine 256 0 0
  let second := Block.periodic 31 1 (Array.replicate 256 1)
  let repeated := Block.periodic 32 1 (Array.replicate 256 0)
  rw [truncation_shape]
  change getFromBlocks ([first, second] ++ List.replicate 7 repeated) n = _
  by_cases low : n < 256
  · have value : n / 256 % 32 = 0 := by omega
    simp [getFromBlocks, first, Block.get?, Block.length, low, value]
  · by_cases middle : n < 8192
    · have extent : n - 256 < 7936 := by omega
      have outside : ¬ n < 256 := low
      simp only [List.cons_append, List.nil_append, getFromBlocks, first,
        Block.length, if_neg outside, second, Array.size_replicate,
        Nat.reduceMul, if_pos extent]
      have value : 1 + (n - 256) / 256 = n / 256 % 32 := by omega
      exact (repeated_value 31 1 (n - 256) extent).trans (congrArg some value)
    · have offset : (([first, second].map Block.length).sum) = 8192 := by
        simp [first, second, Block.length]
      have tail := skip_blocks [first, second] (List.replicate 7 repeated) (n - 8192)
      have index : 8192 + (n - 8192) = n := by omega
      rw [offset, index] at tail
      rw [tail]
      have extent : n - 8192 < 7 * repeated.length := by
        simp only [repeated, Block.length, Array.size_replicate, Nat.reduceMul]
        omega
      rw [Verification.ShiftKeys.repeated_get repeated 7 (n - 8192) extent]
      have remainder : (n - 8192) % 8192 < 8192 := Nat.mod_lt _ (by decide)
      have value : 0 + ((n - 8192) % 8192) / 256 = n / 256 % 32 := by omega
      simpa only [repeated, Block.length, Array.size_replicate, Nat.reduceMul, value] using
        repeated_value 32 0 ((n - 8192) % 8192) remainder

end Airbender.UnifiedReduced.Setup.Proofs
