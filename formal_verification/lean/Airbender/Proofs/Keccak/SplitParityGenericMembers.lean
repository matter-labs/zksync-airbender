import Airbender.Data.Setup.Keccak.ColumnParityGeneric
import Airbender.Proofs.Keccak.SplitParityIotaLookup
import Airbender.Proofs.Keccak.SplitParitySlotLookup
import Airbender.Proofs.Keccak.SplitParityControllerLookup
import Airbender.Proofs.Keccak.SplitXor5Lookup

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Every generic membership comes from one complete retained region or native zero padding. -/
theorem column_parity_generic_member (row : Vector (ZMod babyBearModulus) 8)
    (sound : columnParityGenericTable.toRaw.Soundness #[] row) :
    (columnParityIota.table "Airbender.SplitColumnParityIota").toRaw.Soundness #[] row ∨
      (columnParitySlots.table "Airbender.SplitColumnParitySlots").toRaw.Soundness #[] row ∨
      (columnParityControl.table "Airbender.SplitColumnParityControl").toRaw.Soundness #[] row ∨
      (columnParityXor5.table "Airbender.SplitColumnParityXor5").toRaw.Soundness #[] row ∨
      row = Vector.replicate 8 0 := by
  change ∃ index : Fin columnParityGenericLength,
    row = (columnParityGenericRow index).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  unfold columnParityGenericRow
  split_ifs
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    refine ⟨⟨index.val - 65780, by change index.val - 65780 < 1048576; omega⟩, ?_⟩
    simp [Vector.map_map, Function.comp_def, fromElements]
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    simp only [Vector.map_replicate, Int.cast_zero]

/-- The retained native byte-iota region has its complete discriminator. -/
theorem column_parity_iota_table_tag (row : Vector (ZMod babyBearModulus) 8)
    (sound : (columnParityIota.table "Airbender.SplitColumnParityIota").toRaw.Soundness #[] row) :
    row[7] = 38 := by
  change ∃ index : Fin columnParityIota.length,
    row = (columnParityIota.row index).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  rw [column_parity_iota_field_row]
  simp [Airbender.Keccak.byteRow]

/-- The retained slot region has its complete native discriminator. -/
theorem column_parity_slot_table_tag (row : Vector (ZMod babyBearModulus) 8)
    (sound : (columnParitySlots.table "Airbender.SplitColumnParitySlots").toRaw.Soundness #[] row) :
    row[7] = 62 := by
  change ∃ index : Fin columnParitySlots.length,
    row = (columnParitySlots.row index).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  simp only [TableData.row, Vector.getElem_map]
  change (signedValue (((Column.mk #[.affine 122 62 0]).get? (0 + index.val)).getD 0) : ZMod babyBearModulus) = 62
  have bound : index.val < 122 := index.isLt
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound, signedValue, babyBearModulus]

/-- The retained control region has its complete native discriminator. -/
theorem column_parity_control_table_tag (row : Vector (ZMod babyBearModulus) 8)
    (sound : (columnParityControl.table "Airbender.SplitColumnParityControl").toRaw.Soundness #[] row) :
    row[7] = 63 := by
  change ∃ index : Fin columnParityControl.length,
    row = (columnParityControl.row index).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  simp only [TableData.row, Vector.getElem_map]
  change (signedValue (((Column.mk #[.affine 122 63 0]).get? (0 + index.val)).getD 0) : ZMod babyBearModulus) = 63
  have bound : index.val < 122 := index.isLt
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound, signedValue, babyBearModulus]

/-- Actual native discriminators select their complete retained region. -/
theorem column_parity_generic_bindings (row : Vector (ZMod babyBearModulus) 8)
    (sound : columnParityGenericTable.toRaw.Soundness #[] row) :
    (row[7] = 38 → (columnParityIota.table "Airbender.SplitColumnParityIota").toRaw.Soundness #[] row) ∧
      (row[7] = 62 → (columnParitySlots.table "Airbender.SplitColumnParitySlots").toRaw.Soundness #[] row) ∧
      (row[7] = 63 → (columnParityControl.table "Airbender.SplitColumnParityControl").toRaw.Soundness #[] row) ∧
      (row[7] = 64 → (columnParityXor5.table "Airbender.SplitColumnParityXor5").toRaw.Soundness #[] row) := by
  have val38 : (38 : ZMod babyBearModulus).val = 38 := by rfl
  have val62 : (62 : ZMod babyBearModulus).val = 62 := by rfl
  have val63 : (63 : ZMod babyBearModulus).val = 63 := by rfl
  have val64 : (64 : ZMod babyBearModulus).val = 64 := by rfl
  rcases column_parity_generic_member row sound with iota | slots | control | parity | padding
  · have tag := column_parity_iota_table_tag row iota
    refine ⟨fun _ => iota, ?_, ?_, ?_⟩
    all_goals intro other; have impossible := congrArg ZMod.val (tag.symm.trans other)
    all_goals norm_num only [val38, val62, val63, val64, ZMod.val_zero] at impossible
  · have tag := column_parity_slot_table_tag row slots
    refine ⟨?_, fun _ => slots, ?_, ?_⟩
    all_goals intro other; have impossible := congrArg ZMod.val (tag.symm.trans other)
    all_goals norm_num only [val38, val62, val63, val64, ZMod.val_zero] at impossible
  · have tag := column_parity_control_table_tag row control
    refine ⟨?_, ?_, fun _ => control, ?_⟩
    all_goals intro other; have impossible := congrArg ZMod.val (tag.symm.trans other)
    all_goals norm_num only [val38, val62, val63, val64, ZMod.val_zero] at impossible
  · have tag := (xor5_table_sound row parity).2.2.2.2
    refine ⟨?_, ?_, ?_, fun _ => parity⟩
    all_goals intro other; have impossible := congrArg ZMod.val (tag.symm.trans other)
    all_goals norm_num only [val38, val62, val63, val64, ZMod.val_zero] at impossible
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals intro other; rw [padding] at other
    all_goals have impossible := congrArg ZMod.val other
    all_goals norm_num only [Vector.getElem_replicate, val38, val62, val63, val64, ZMod.val_zero] at impossible

end Airbender.Keccak.Split.Native.Fixed.Proofs
