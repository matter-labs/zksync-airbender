import Airbender.Review.Helpers.Tables.NativeShiftScalarData
import Airbender.Review.Helpers.Tables.ShiftScalars
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.ShiftScalarProofs
open Setup NativeShiftScalars
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem stored_blocks : dataSignFill.columns[1].blocks.toList =
    [.affine 1146880 0 0,
    .affine 32768 32768 0,
    .affine 32768 0 0,
    .affine 32768 49152 0,
    .affine 32768 0 0,
    .affine 32768 57344 0,
    .affine 32768 0 0,
    .affine 32768 61440 0,
    .affine 32768 0 0,
    .affine 32768 63488 0,
    .affine 32768 0 0,
    .affine 32768 64512 0,
    .affine 32768 0 0,
    .affine 32768 65024 0,
    .affine 32768 0 0,
    .affine 32768 65280 0,
    .affine 32768 0 0,
    .affine 32768 65408 0,
    .affine 32768 0 0,
    .affine 32768 65472 0,
    .affine 32768 0 0,
    .affine 32768 65504 0,
    .affine 32768 0 0,
    .affine 32768 65520 0,
    .affine 32768 0 0,
    .affine 32768 65528 0,
    .affine 32768 0 0,
    .affine 32768 65532 0,
    .affine 32768 0 0,
    .affine 32768 65534 0] := rfl

/-- Each of the 64 half-limb domains uses actual constant stored blocks.
    Bounds select a block symbolically; no two-million-row enumeration. -/
theorem sign_low (i : Fin 2097152) :
    dataSignFill.columns[1].get? i.val = some (signFillLow i.val) := by
  have chunks : i.val / 32768 < 64 := by have := i.isLt; omega
  rw [Column.get?,stored_blocks]
  interval_cases chunk : i.val / 32768
  all_goals
    have shift : i.val / 65536 = (i.val / 32768) / 2 := by omega
    rw [chunk] at shift
    by_cases sign : i.val % 65536 < 32768
    all_goals
      first
      | omega
      | simp only [signFillLow]
        first | rw [if_pos sign] | rw [if_neg sign]
        try rw [shift]
        norm_num only
        repeat' first
          | rw [getFromBlocks,if_neg (by dsimp only [Block.length]; omega)]
          | rw [getFromBlocks,if_pos (by dsimp only [Block.length]; omega)]
        simp only [Block.get?,Block.length]
        rw [if_pos (by omega)]
        simp only [Int.natCast_zero,Int.zero_mul,Int.add_zero,
          if_pos (Int.natCast_nonneg _),Int.toNat_natCast]
        all_goals rfl

end Airbender.Verification.ShiftScalarProofs
