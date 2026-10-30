import Airbender.Proofs.Keccak.SplitParityControllerKeys
import Airbender.Proofs.Keccak.SplitScheduleControl

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private theorem control_key_small : ∀ index : Fin 361,
    controlAt index.val + 2048 < babyBearModulus := by
  decide +kernel

/-- Exact native slot-table membership binds all six original physical lanes. -/
theorem column_parity_slot_table_sound [Fact babyBearModulus.Prime]
    (row : Vector (ZMod babyBearModulus) 8)
    (sound : (columnParitySlots.table "Airbender.SplitColumnParitySlots").toRaw.Soundness #[] row)
    (index : Fin 361)
    (key : row[0] = ((controlAt index.val + 2048 : Nat) : ZMod babyBearModulus)) :
    ∀ lane : Fin 6, row[1 + lane.val] = ((Call.slots index)[lane.val].val : ZMod babyBearModulus) := by
  change ∃ i : Fin columnParityControl.length,
    row = (columnParitySlots.row ⟨i.val, i.isLt⟩).map
      (fun value : Int => (value : ZMod babyBearModulus)) at sound
  obtain ⟨i, rfl⟩ := sound
  have sourceKey := column_parity_slot_key i
  by_cases padding : i.val = 0
  · rw [if_pos padding] at sourceKey
    have mapped := congrArg (fun value : Int => (value : ZMod babyBearModulus)) sourceKey
    have zero : ((columnParitySlots.row ⟨i.val, i.isLt⟩).map
        (fun value : Int => (value : ZMod babyBearModulus)))[0] = 0 := by
      simpa only [Vector.getElem_map, Int.cast_zero] using mapped
    have impossible := congrArg ZMod.val (zero.symm.trans key)
    rw [ZMod.val_zero, ZMod.val_natCast_of_lt (control_key_small index)] at impossible
    omega
  · rw [if_neg padding] at sourceKey
    have mapped := congrArg (fun value : Int => (value : ZMod babyBearModulus)) sourceKey
    have actual : ((columnParitySlots.row ⟨i.val, i.isLt⟩).map
        (fun value : Int => (value : ZMod babyBearModulus)))[0] =
        ((controlAt (columnParityControllerIndex i).val + 2048 : Nat) : ZMod babyBearModulus) := by
      simpa only [Vector.getElem_map, Int.cast_natCast] using mapped
    have numeric := congrArg ZMod.val (actual.symm.trans key)
    rw [ZMod.val_natCast_of_lt (control_key_small (columnParityControllerIndex i)),
      ZMod.val_natCast_of_lt (control_key_small index)] at numeric
    have same := Split.Proofs.control_injective
      (show controlAt (columnParityControllerIndex i).val = controlAt index.val by omega)
    have enabled : (columnParityControl.row i)[1] = 1 := by
      rw [column_parity_controller_execute_value, if_neg padding]
    intro lane
    have slots := (column_parity_controller_slots i enabled).2 lane
    have values := congrArg (fun value : Int => (value : ZMod babyBearModulus)) slots
    simpa only [Vector.getElem_map, Int.cast_natCast, same] using values

end Airbender.Keccak.Split.Native.Fixed.Proofs
