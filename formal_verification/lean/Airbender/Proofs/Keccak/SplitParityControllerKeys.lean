import Airbender.Proofs.Keccak.SplitParityControllerRows

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000

/-- The leading native controller row is padding; every other retained row executes. -/
theorem column_parity_controller_execute_value : ∀ i : Fin columnParityControl.length,
    (columnParityControl.row i)[1] = if i.val = 0 then 0 else 1 := by
  intro i
  fin_cases i <;> exact of_decide_eq_true (by cbv)

/-- Every retained slot key contains the complete control word and execute-key offset. -/
theorem column_parity_slot_key (i : Fin columnParityControl.length) :
    (columnParitySlots.row ⟨i.val, i.isLt⟩)[0] = if i.val = 0 then 0
      else ((controlAt (columnParityControllerIndex i).val + 2048 : Nat) : Int) := by
  by_cases zero : i.val = 0
  · have same : i = ⟨0, by decide⟩ := Fin.ext zero
    subst i
    exact of_decide_eq_true (by cbv)
  · rw [if_neg zero]
    have enabled : (columnParityControl.row i)[1] = 1 := by
      rw [column_parity_controller_execute_value, if_neg zero]
    exact (column_parity_controller_slots i enabled).1

end Airbender.Keccak.Split.Native.Fixed.Proofs
