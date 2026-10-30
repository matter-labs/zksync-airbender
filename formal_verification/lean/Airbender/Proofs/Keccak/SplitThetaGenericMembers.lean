import Airbender.Data.Setup.Keccak.ThetaRhoPhysical
import Airbender.Proofs.Keccak.SplitThetaSplitLookup
import Airbender.Proofs.Keccak.SplitThetaControllerLookup
import Airbender.Proofs.Keccak.SplitThetaSlotLookup

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
open Airbender.Setup
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- Complete native generic membership selects one retained region or physical zero padding. -/
theorem theta_rho_physical_generic_member (row : Vector (ZMod babyBearModulus) 9)
    (sound : thetaRhoPhysicalGenericTable.toRaw.Soundness #[] row) :
    (thetaRhoXor.table "Airbender.SplitThetaRhoXor").toRaw.Soundness #[] row ∨
      (thetaRhoXorSplit.table "Airbender.SplitThetaRhoXorSplit").toRaw.Soundness #[] row ∨
      (thetaRhoControl.table "Airbender.SplitThetaRhoControl").toRaw.Soundness #[] row ∨
      (thetaRhoSlots.table "Airbender.SplitThetaRhoSlots").toRaw.Soundness #[] row ∨
      row = Vector.replicate 9 0 := by
  change ∃ index : Fin thetaRhoPhysicalGenericLength,
    row = (thetaRhoPhysicalGenericRow index).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  unfold thetaRhoPhysicalGenericRow
  split_ifs with first second third fourth
  · apply Or.inl
    refine ⟨⟨index.val, first⟩, ?_⟩
    simp [Vector.map_map, Function.comp_def, fromElements]
  · apply Or.inr; apply Or.inl
    refine ⟨⟨index.val - 65536, by change index.val - 65536 < 524288; omega⟩, ?_⟩
    simp [Vector.map_map, Function.comp_def, fromElements]
  · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    simp only [Vector.map_replicate, Int.cast_zero]

/-- The actual native control region retains its complete discriminator. -/
theorem theta_rho_physical_control_tag (row : Vector (ZMod babyBearModulus) 9)
    (sound : (thetaRhoControl.table "Airbender.SplitThetaRhoControl").toRaw.Soundness #[] row) :
    row[8] = 59 := by
  change ∃ index : Fin thetaRhoControl.length,
    row = (thetaRhoControl.row index).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  simp only [TableData.row, Vector.getElem_map]
  change (signedValue (((Column.mk #[.affine 121 59 0]).get? (0 + index.val)).getD 0) : ZMod babyBearModulus) = 59
  have bound : index.val < 121 := index.isLt
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound, signedValue, babyBearModulus]

/-- The actual native slot region retains its complete discriminator. -/
theorem theta_rho_physical_slot_tag (row : Vector (ZMod babyBearModulus) 9)
    (sound : (thetaRhoSlots.table "Airbender.SplitThetaRhoSlots").toRaw.Soundness #[] row) :
    row[8] = 60 := by
  change ∃ index : Fin thetaRhoSlots.length,
    row = (thetaRhoSlots.row index).map (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨index, rfl⟩ := sound
  simp only [TableData.row, Vector.getElem_map]
  change (signedValue (((Column.mk #[.affine 121 60 0]).get? (0 + index.val)).getD 0) : ZMod babyBearModulus) = 60
  have bound : index.val < 121 := index.isLt
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound, signedValue, babyBearModulus]

/-- Actual native discriminators select exact membership in their complete retained region. -/
theorem theta_rho_physical_generic_bindings (row : Vector (ZMod babyBearModulus) 9)
    (sound : thetaRhoPhysicalGenericTable.toRaw.Soundness #[] row) :
    (row[8] = 4 → (thetaRhoXor.table "Airbender.SplitThetaRhoXor").toRaw.Soundness #[] row) ∧
      (row[8] = 58 → (thetaRhoXorSplit.table "Airbender.SplitThetaRhoXorSplit").toRaw.Soundness #[] row) ∧
      (row[8] = 59 → (thetaRhoControl.table "Airbender.SplitThetaRhoControl").toRaw.Soundness #[] row) ∧
      (row[8] = 60 → (thetaRhoSlots.table "Airbender.SplitThetaRhoSlots").toRaw.Soundness #[] row) := by
  have val4 : (4 : ZMod babyBearModulus).val = 4 := by rfl
  have val58 : (58 : ZMod babyBearModulus).val = 58 := by rfl
  have val59 : (59 : ZMod babyBearModulus).val = 59 := by rfl
  have val60 : (60 : ZMod babyBearModulus).val = 60 := by rfl
  rcases theta_rho_physical_generic_member row sound with xor | fragment | control | slots | padding
  · have tag := (xor_byte_table_sound row xor).2.2.2.2.2
    refine ⟨fun _ => xor, ?_, ?_, ?_⟩
    all_goals intro other; have impossible := congrArg ZMod.val (tag.symm.trans other)
    all_goals norm_num only [val4, val58, val59, val60, ZMod.val_zero] at impossible
  · have tag := (theta_split_table_sound row fragment).2.2.2.2.2.2.2.2
    refine ⟨?_, fun _ => fragment, ?_, ?_⟩
    all_goals intro other; have impossible := congrArg ZMod.val (tag.symm.trans other)
    all_goals norm_num only [val4, val58, val59, val60, ZMod.val_zero] at impossible
  · have tag := theta_rho_physical_control_tag row control
    refine ⟨?_, ?_, fun _ => control, ?_⟩
    all_goals intro other; have impossible := congrArg ZMod.val (tag.symm.trans other)
    all_goals norm_num only [val4, val58, val59, val60, ZMod.val_zero] at impossible
  · have tag := theta_rho_physical_slot_tag row slots
    refine ⟨?_, ?_, ?_, fun _ => slots⟩
    all_goals intro other; have impossible := congrArg ZMod.val (tag.symm.trans other)
    all_goals norm_num only [val4, val58, val59, val60, ZMod.val_zero] at impossible
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals intro other; rw [padding] at other
    all_goals have impossible := congrArg ZMod.val other
    all_goals norm_num only [Vector.getElem_replicate, val4, val58, val59, val60, ZMod.val_zero] at impossible

end Airbender.Keccak.Split.Native.Fixed.Proofs
