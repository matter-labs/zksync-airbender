import Airbender.Proofs.Tables.SignFillBlocks

namespace Airbender.Verification.ShiftScalarProofs
open Setup NativeShiftScalars
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem sign_high_part0 (i : Fin 2097152)
    (lower : 0 ≤ i.val / 32768) (upper : i.val / 32768 < 16) :
    dataSignFill.columns[2].get? i.val = some (signFillHigh i.val) := by
  rw [Column.get?,sign_high_blocks]
  interval_cases chunk : i.val / 32768
  all_goals
    have shift : i.val / 65536 = (i.val / 32768) / 2 := by omega
    rw [chunk] at shift
    by_cases sign : i.val % 65536 < 32768
    all_goals
      first
      | omega
      | simp only [signFillHigh]
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
