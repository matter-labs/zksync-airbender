import Airbender.Review.Helpers.Tables.Range

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Airbender.Verification
open Setup

private theorem affine_zero_get (b t n : Nat) (hn : n < b + t) :
    ((Column.mk #[.affine b 0 1, .affine t 0 0]).get? n) =
      some (if n < b then n else 0) := by
  by_cases h : n < b
  · simp [Column.get?, getFromBlocks, Block.get?, Block.length, h]
  · have ht : n - b < t := by omega
    simp [Column.get?, getFromBlocks, Block.get?, Block.length, h, ht]

private theorem affine_range_value (b t n : Nat) (hn : n < b + t)
    (hb : b ≤ babyBearModulus / 2) :
    signedValue (((Column.mk #[.affine b 0 1, .affine t 0 0]).get? n).getD 0) =
      ((if n < b then n else 0 : Nat) : Int) := by
  rw [affine_zero_get b t n hn]
  simp only [Option.getD_some]
  have half : (if n < b then n else 0) ≤ babyBearModulus / 2 := by split_ifs <;> omega
  exact if_pos half

theorem imported_range16_row (i : Fin importedRange16.length) :
    (importedRange16.row i)[0] = ((if i.val < 65536 then i.val else 0 : Nat) : Int) := by
  simp only [TableData.row, Vector.getElem_map]
  have column : importedRange16.columns[0] = Column.mk #[.affine 65536 0 1, .affine 16711680 0 0] := by decide
  have offset : importedRange16.offset = 0 := by decide
  rw [column, offset, Nat.zero_add]
  exact affine_range_value _ _ _ i.isLt (by decide)

theorem imported_timestamp_row (i : Fin importedTimestamp19.length) :
    (importedTimestamp19.row i)[0] = ((if i.val < 524288 then i.val else 0 : Nat) : Int) := by
  simp only [TableData.row, Vector.getElem_map]
  have column : importedTimestamp19.columns[0] = Column.mk #[.affine 524288 0 1, .affine 16252928 0 0] := by decide
  have offset : importedTimestamp19.offset = 0 := by decide
  rw [column, offset, Nat.zero_add]
  exact affine_range_value _ _ _ i.isLt (by decide)

private theorem range13_prefix (n : Nat) :
    1316864 + n - 262144 - 1048576 - 2048 - 4096 = n ∧
    ¬ 1316864 + n < 262144 ∧
    ¬ 1316864 + n - 262144 < 1048576 ∧
    ¬ 1316864 + n - 262144 - 1048576 < 2048 ∧
    ¬ 1316864 + n - 262144 - 1048576 - 2048 < 4096 := by omega

theorem imported_range13_row (i : Fin importedRange13.length) :
    (importedRange13.row i)[0] = (i.val : Int) := by
  have bound := i.isLt
  change i.val < 8192 at bound
  have half : i.val ≤ babyBearModulus / 2 := by norm_num [babyBearModulus]; omega
  obtain ⟨shifted, skip0, skip1, skip2, skip3⟩ := range13_prefix i.val
  simp only [TableData.row, Vector.getElem_map]
  have column : (importedRange13.columns[0]'(by decide)) = Column.mk #[
      .periodic 512 1 (Array.replicate 512 0),
      .periodic 1024 1 (Array.replicate 1024 0),
      .affine 2048 0 1, .affine 4096 0 1, .affine 8192 0 1,
      .affine 65536 0 1, .affine 2803712 0 0] := by rfl
  have offset : importedRange13.offset = 1316864 := by decide
  rw [column, offset]
  simp [Column.get?, getFromBlocks, Block.length, Block.get?,
    shifted, signedValue, half, bound, skip0, skip1, skip2, skip3]

theorem imported_scalar_range_iff {p : Nat} [Fact p.Prime]
    (data : TableData 1) (bound : Nat) (positive : 0 < bound) (extent : bound ≤ data.length)
    (rows : ∀ i : Fin data.length,
      (data.row i)[0] = ((if i.val < bound then i.val else 0 : Nat) : Int))
    (value : ZMod p) :
    (∃ i : Fin data.length, value = ((data.row i)[0] : ZMod p)) ↔ value.val < bound := by
  constructor
  · rintro ⟨i, rfl⟩
    rw [rows]
    simp only [Int.cast_natCast, ZMod.val_natCast]
    have small : (if i.val < bound then i.val else 0) < bound := by split_ifs <;> omega
    exact lt_of_le_of_lt (Nat.mod_le _ _) small
  · intro h
    let i : Fin data.length := ⟨value.val, by omega⟩
    refine ⟨i, ?_⟩
    rw [rows]
    simp only [i, h, ↓reduceIte, Int.cast_natCast]
    exact (ZMod.natCast_zmod_val value).symm

theorem imported_range16_iff {p : Nat} [Fact p.Prime] (value : ZMod p) :
    (∃ i : Fin importedRange16.length, value = ((importedRange16.row i)[0] : ZMod p)) ↔
      value.val < 65536 :=
  imported_scalar_range_iff importedRange16 65536 (by decide) (by decide)
    imported_range16_row value

theorem imported_range13_iff {p : Nat} [Fact p.Prime] (value : ZMod p) :
    (∃ i : Fin importedRange13.length, value = ((importedRange13.row i)[0] : ZMod p)) ↔
      value.val < 8192 := by
  apply imported_scalar_range_iff importedRange13 8192 (by decide) (by decide)
  intro i
  rw [if_pos (show i.val < 8192 from i.isLt)]
  exact imported_range13_row i

theorem imported_timestamp_iff {p : Nat} [Fact p.Prime] (value : ZMod p) :
    (∃ i : Fin importedTimestamp19.length, value = ((importedTimestamp19.row i)[0] : ZMod p)) ↔
      value.val < 524288 :=
  imported_scalar_range_iff importedTimestamp19 524288 (by decide) (by decide)
    imported_timestamp_row value

end Airbender.Verification
