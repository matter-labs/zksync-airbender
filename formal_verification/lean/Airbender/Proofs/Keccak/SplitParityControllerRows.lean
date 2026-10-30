import Airbender.Data.Setup.Keccak.ColumnParityControl
import Airbender.Review.Circuits.Keccak.SplitCall
import Airbender.Proofs.Keccak.SplitSlotReduction

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000

/-- Retained controller-row order, including the final delayed-iota call. -/
def columnParityControllerIndex (i : Fin columnParityControl.length) : Fin 361 :=
  ⟨15 * ((i.val - 1) / 5) + (i.val - 1) % 5, by
    have bound := i.isLt
    change i.val < 122 at bound
    omega⟩

/-- The native controller retains the execute bit, control transition and iota round. -/
theorem column_parity_controller_schedule : ∀ i : Fin columnParityControl.length,
    (columnParityControl.row i)[1] = 1 →
      kindAt (columnParityControllerIndex i).val = .columnParity ∧
      (columnParityControl.row i)[0] = (controlAt (columnParityControllerIndex i).val : Int) ∧
      (columnParityControl.row i)[2] = (bump (controlAt (columnParityControllerIndex i).val) : Int) ∧
      (columnParityControl.row i)[3] =
        ((if (columnParityControllerIndex i).val % 5 = 0 then
          (columnParityControllerIndex i).val / 15 else 0 : Nat) : Int) := by
  intro i
  fin_cases i <;> exact of_decide_eq_true (by cbv)

/-- The separate slot table uses the compiler's execute-key offset and original lane layout. -/
theorem column_parity_controller_slots : ∀ i : Fin columnParityControl.length,
    (columnParityControl.row i)[1] = 1 →
      let slotRow := columnParitySlots.row ⟨i.val, by have := i.isLt; exact this⟩
      slotRow[0] = ((controlAt (columnParityControllerIndex i).val + 2048 : Nat) : Int) ∧
      ∀ lane : Fin 6, slotRow[1 + lane.val] =
        ((Call.slots (columnParityControllerIndex i))[lane.val].val : Int) := by
  simp only [Call.Proofs.slots_normalized]
  decide +kernel

/-- Only the retained live rows execute; the separate leading row is padding. -/
theorem column_parity_controller_execute : ∀ i : Fin columnParityControl.length,
    (columnParityControl.row i)[1] = 0 ∨ (columnParityControl.row i)[1] = 1 := by
  intro i
  fin_cases i <;> exact of_decide_eq_true (by cbv)

end Airbender.Keccak.Split.Native.Fixed.Proofs
