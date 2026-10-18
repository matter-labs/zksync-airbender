import Airbender.Review.Circuits.WordMemory.Tables.NativeSetupData
import Airbender.Proofs.WordMemory.PhysicalSetup
import Airbender.Proofs.Tables.ZeroTail

namespace Airbender.WordMemory.Proofs
open Verification Setup Native Reference.RiscV.Sail

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem rom_key (i : Fin 1048576) :
    exportedROM.columns[0].get? i.val = some (4 * i.val) := by
  change getFromBlocks [.affine 1048576 0 4] i.val = _
  rw [getFromBlocks]
  simp only [Block.length]
  rw [if_pos i.isLt]
  simpa using affine_get 1048576 0 4 i.val i.isLt

private theorem rom_tag (i : Fin 1048576) :
    exportedROM.columns[3].get? i.val = some 24 := by
  change getFromBlocks [.affine 1048576 24 0] i.val = _
  rw [getFromBlocks]
  simp only [Block.length]
  rw [if_pos i.isLt]
  simpa using affine_get 1048576 24 0 i.val i.isLt

private theorem rom_low (i : Fin 1048576) :
    exportedROM.columns[1].get? i.val = some ((programROM.zeroPadded.word i.val).toNat % 65536) := by
  rcases i with ⟨n, bound⟩
  change exportedROM.columns[1].get? n = some ((programROM.zeroPadded.word n).toNat % 65536)
  by_cases early : n < 4
  · rw [zero_padding_prefix _ (by simpa [programROM] using early)]
    interval_cases n <;> decide
  · rw [zero_padding_tail _ (by simpa [programROM] using Nat.le_of_not_gt early) bound]
    change getFromBlocks [.dense #[41347, 43043, 40963, 4211], .affine 1048572 0 0] n = some 0
    rw [getFromBlocks]
    change (if n < 4 then _ else _) = _
    rw [if_neg early, getFromBlocks]
    change (if n - 4 < 1048572 then _ else _) = _
    rw [if_pos (by omega)]
    simpa [Block.length] using affine_get 1048572 0 0 (n - 4) (by omega)

private theorem rom_high (i : Fin 1048576) :
    exportedROM.columns[2].get? i.val = some ((programROM.zeroPadded.word i.val).toNat / 65536) := by
  rcases i with ⟨n, bound⟩
  change exportedROM.columns[2].get? n = some ((programROM.zeroPadded.word n).toNat / 65536)
  by_cases early : n < 4
  · rw [zero_padding_prefix _ (by simpa [programROM] using early)]
    interval_cases n <;> decide
  · rw [zero_padding_tail _ (by simpa [programROM] using Nat.le_of_not_gt early) bound]
    change getFromBlocks [.dense #[256, 48, 256, 49152], .affine 1048572 0 0] n = some 0
    rw [getFromBlocks]
    change (if n < 4 then _ else _) = _
    rw [if_neg early, getFromBlocks]
    change (if n - 4 < 1048572 then _ else _) = _
    rw [if_pos (by omega)]
    simpa [Block.length] using affine_get 1048572 0 0 (n - 4) (by omega)

/-- Every actual exported ROM tuple, not only the sample prefix, agrees with
    the independently constructed native-shaped ROM model and native tag 24. -/
theorem exported_rom_rows (i : Fin 1048576) :
    exportedROM.rowNat i = (programROM.zeroPadded.row i).push 24 := by
  ext k bound
  interval_cases k <;>
    simp [TableData.rowNat, WordROM.row, rom_key, rom_low, rom_high, rom_tag]

theorem exported_range_rows (i : Fin 65536) : exportedRange16.rowNat i = #v[i.val] := by
  have column : exportedRange16.columns[0].get? i.val = some i.val := by
    change getFromBlocks [.affine 65536 0 1] i.val = _
    rw [getFromBlocks]
    simp only [Block.length]
    rw [if_pos i.isLt]
    simpa using affine_get 65536 0 1 i.val i.isLt
  ext k bound
  have : k = 0 := by omega
  subst k
  simp [TableData.rowNat, column]

/-- The native materializer uses a non-PC sentinel in every unsupported slot,
    including the explicit UNIMP input word at index three. -/
theorem exported_decoder_padding (i : Fin 1048576) (padding : 3 ≤ i.val) :
    exportedDecoder.rowNat i = Vector.replicate 10 2147483646 := by
  have column (values : Array Nat) (size : values.size = 3) :
      (getFromBlocks [.dense values, .affine 1048573 2147483646 (Int.ofNat 0)] i.val).getD 0 = 2147483646 := by
    simp only [getFromBlocks, Block.length, size]
    rw [if_neg (by omega : ¬i.val < 3), if_pos (by have := i.isLt; omega)]
    have entry := affine_get 1048573 2147483646 0 (i.val - 3) (by have := i.isLt; omega)
    simpa using congrArg (fun v : Option Nat => v.getD 0) entry
  ext k bound
  interval_cases k <;> simp only [TableData.rowNat, exportedDecoder, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    Vector.getElem_replicate, Column.get?]
  all_goals
    exact column _ rfl

/-- Check the native public image's entire zero tail by its actual stored blocks. -/
theorem exported_image_zero (n : Nat) (lower : 4 ≤ n) (bound : n < 1048576) :
    exportedImage.get? n = some 0 := by
  apply Setup.Proofs.zeroTail_sound 4 _ (by decide) n lower
  simpa [exportedImage, Block.length] using bound

theorem exported_separator_rows (i : Fin 65536) :
    exportedSeparator.rowNat i = (romSeparatorRow i).push 23 := by
  have key : exportedSeparator.columns[0].get? i.val = some i.val := by
    change getFromBlocks [.affine 65536 0 1] i.val = _
    rw [getFromBlocks]
    simp only [Block.length]
    rw [if_pos i.isLt]
    simpa using affine_get 65536 0 1 i.val i.isLt
  have flag : exportedSeparator.columns[1].get? i.val = some (if i.val < 64 then 0 else 1) := by
    change getFromBlocks [.affine 64 0 0, .affine 65472 1 0] i.val = _
    rw [getFromBlocks]
    change (if i.val < 64 then _ else _) = _
    by_cases low : i.val < 64
    · rw [if_pos low]
      simpa [low] using affine_get 64 0 0 i.val low
    · rw [if_neg low, getFromBlocks]
      change (if i.val - 64 < 65472 then _ else _) = _
      rw [if_pos (by have := i.isLt; omega)]
      simpa [Block.length, low] using affine_get 65472 1 0 (i.val - 64) (by have := i.isLt; omega)
  have residue : exportedSeparator.columns[2].get? i.val = some (i.val % 64) := by
    change getFromBlocks [.periodic 1024 0 (Array.range 64)] i.val = _
    rw [getFromBlocks]
    change (if i.val < 65536 then _ else _) = _
    rw [if_pos i.isLt]
    simpa using Setup.Proofs.periodic_get (Array.range 64) 1024 0 i.val (by decide)
      (by simp)
  have tag : exportedSeparator.columns[3].get? i.val = some 23 := by
    change getFromBlocks [.affine 65536 23 0] i.val = _
    rw [getFromBlocks]
    simp only [Block.length]
    rw [if_pos i.isLt]
    simpa using affine_get 65536 23 0 i.val i.isLt
  ext k bound
  interval_cases k <;> simp [TableData.rowNat, romSeparatorRow, key, flag, residue, tag]

/-- Imported literal rows supply physical ROM membership without a table-content
    equivalence premise; their native offset and tag are both checked. -/
theorem exported_rom_physical (i : Fin 1048576) :
    exportedROM.row (p := mersenne31Modulus) i =
      NativeSetup.genericRow programROM.zeroPadded
        ⟨65537 + i.val, by have := i.isLt; omega⟩ := by
  rw [TableData.row, exported_rom_rows]
  simp [NativeSetup.genericRow, show ¬65537 + i.val < 65537 by omega,
    show 65537 + i.val < 1114113 by have := i.isLt; omega]

theorem exported_rom_read {before : Reference.RiscV.Sail.State}
    (image : wordROMImage before 4 = some programROM)
    {key lo hi : ZMod mersenne31Modulus}
    (member : ∃ i : Fin 1048576, exportedROM.row i = (#v[key, lo, hi]).push 24) :
    (Trace.Cell.ram (BitVec.ofNat 32 key.val)).read (paddedROMState before 4) =
      .ok (Arithmetic.Word.mk lo.val hi.val).toBitVec (paddedROMState before 4) := by
  obtain ⟨i, same⟩ := member
  apply physical_rom_read (padded_rom_image image)
  exact ⟨⟨65537 + i.val, by have := i.isLt; omega⟩, (exported_rom_physical i).symm.trans same⟩

end Airbender.WordMemory.Proofs
