import Airbender.Review.Helpers.Tables.PairData
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.ImportedCleanup
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem key (i : Fin 65536) :
    jumpCleanupData.columns[0].get? i.val = some i.val := by
  change getFromBlocks [.affine 65536 0 1] i.val = some i.val
  simp [getFromBlocks, Block.get?, Block.length, i.isLt]

private theorem periodic_bits (n : Nat) (bound : n < 65532) :
    Block.get? (.periodic 16383 0 #[1, 1, 0, 0]) n =
      some (if n % 4 < 2 then 1 else 0) := by
  have hm : n % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases residue : n % 4
  all_goals simp [Block.get?, Block.length, bound, residue]

private theorem bits_size : (#[1, 1, 0, 0] : Array Nat).size = 4 := rfl

private theorem dense_ones (n : Nat) (bound : n < 2) :
    Block.get? (.dense (Array.replicate 2 1)) n = some 1 := by
  simp [Block.get?, Block.length, bound]

private theorem periodic_cleaned (n : Nat) (bound : n < 65532) :
    Block.get? (.periodic 16383 4 (Array.replicate 4 4)) n =
      some (4 + 4 * (n / 4)) := by
  have hm : n % 4 < 4 := Nat.mod_lt _ (by decide)
  simp [Block.get?, Block.length, bound, hm]
  simpa only [Int.natCast_add, Int.natCast_mul, Int.natCast_ediv, Nat.cast_ofNat] using
    And.intro (Int.natCast_nonneg (4 + 4 * (n / 4)))
      (Int.toNat_natCast (4 + 4 * (n / 4)))

private theorem bit1 (i : Fin 65536) :
    jumpCleanupData.columns[1].get? i.val = some (i.val / 2 % 2) := by
  change getFromBlocks [.affine 2 0 0, .periodic 16383 0 #[1, 1, 0, 0],
    .dense (Array.replicate 2 1)] i.val = _
  have bound := i.isLt
  by_cases leading : i.val < 2
  · have result : i.val / 2 % 2 = 0 := by omega
    simp [getFromBlocks, Block.get?, Block.length, leading, result]
  · by_cases middle : i.val < 65534
    · have rest : i.val - 2 < 65532 := by omega
      simp only [getFromBlocks, Block.length, bits_size, Nat.reduceMul,
        if_neg leading, if_pos rest]
      have value : (if (i.val - 2) % 4 < 2 then 1 else 0) = i.val / 2 % 2 := by
        split_ifs <;> omega
      exact (periodic_bits _ rest).trans (congrArg some value)
    · have result : i.val / 2 % 2 = 1 := by omega
      have rest : ¬ i.val - 2 < 65532 := by omega
      have tail : i.val - 2 - 65532 < 2 := by omega
      simp only [getFromBlocks, Block.length, bits_size, Array.size_replicate,
        Nat.reduceMul, if_neg leading, if_neg rest, if_pos tail, result]
      exact dense_ones _ tail

private theorem cleaned (i : Fin 65536) :
    jumpCleanupData.columns[2].get? i.val = some (i.val - i.val % 4) := by
  change getFromBlocks [.affine 4 0 0,
    .periodic 16383 4 (Array.replicate 4 4)] i.val = _
  have bound := i.isLt
  by_cases leading : i.val < 4
  · have result : i.val - i.val % 4 = 0 := by omega
    simp [getFromBlocks, Block.get?, Block.length, leading, result]
  · have rest : i.val - 4 < 65532 := by omega
    simp only [getFromBlocks, Block.length, Array.size_replicate,
      Nat.reduceMul, if_neg leading, if_pos rest]
    have value : 4 + 4 * ((i.val - 4) / 4) = i.val - i.val % 4 := by omega
    exact (periodic_cleaned _ rest).trans (congrArg some value)

/-- All three meaningful columns of the actual exported JALR cleanup region. -/
theorem cleanup_row (i : Fin 65536) :
    setupTripleRow jumpCleanupData (by decide) i =
      (i.val, i.val / 2 % 2, i.val - i.val % 4) := by
  simp only [setupTripleRow, show jumpCleanupData.offset = 0 from rfl, Nat.zero_add,
    key i, bit1 i, cleaned i, Option.getD_some]

end Airbender.Verification.ImportedCleanup
