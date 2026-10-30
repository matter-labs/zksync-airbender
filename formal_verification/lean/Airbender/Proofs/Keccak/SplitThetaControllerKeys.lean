import Airbender.Proofs.Keccak.SplitThetaControllerRows

namespace Airbender.Keccak.Split.Native.Fixed.Proofs
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000

/-- The exact leading padding row disables the controller. Every other row executes. -/
theorem theta_rho_controller_execute_value : ∀ i : Fin thetaRhoControl.length,
    (thetaRhoControl.row i)[1] = if i.val = 0 then 0 else 1 := by
  decide +kernel

/-- The actual slot-table key retains the complete native execute-key offset. -/
theorem theta_rho_slot_key : ∀ i : Fin thetaRhoControl.length,
    (thetaRhoSlots.row ⟨i.val, i.isLt⟩)[0] =
      if i.val = 0 then 0 else ((controlAt (thetaRhoControllerIndex i).val + 2048 : Nat) : Int) := by
  decide +kernel

end Airbender.Keccak.Split.Native.Fixed.Proofs
