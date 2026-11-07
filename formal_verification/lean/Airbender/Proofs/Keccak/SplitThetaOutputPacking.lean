import Airbender.Proofs.Keccak.SplitThetaOutputBytes

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- All actual selected state write limbs have their canonical bounded byte expansion. -/
theorem theta_write_limb_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column lane : Fin 5) (limb : Fin 4)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0) :
    (thetaLaneLimb cached true w ⟨lane.val, by omega⟩ limb).val < 65536 ∧
      (thetaLaneLimb cached true w ⟨lane.val, by omega⟩ limb).val =
        (thetaOutputByte cached w lane (Call.rotations[column][lane]) ⟨2 * limb.val, by omega⟩).val +
          256 * (thetaOutputByte cached w lane (Call.rotations[column][lane]) ⟨2 * limb.val + 1, by omega⟩).val := by
  have low := theta_output_byte_bound cached w holds column lane ⟨2 * limb.val, by omega⟩ flags
  have high := theta_output_byte_bound cached w holds column lane ⟨2 * limb.val + 1, by omega⟩ flags
  have equation := theta_native_selected_output cached w holds column lane limb flags
  change thetaLaneLimb cached true w ⟨lane.val, by omega⟩ limb =
    thetaOutputByte cached w lane (Call.rotations[column][lane]) ⟨2 * limb.val, by omega⟩ +
      256 * thetaOutputByte cached w lane (Call.rotations[column][lane]) ⟨2 * limb.val + 1, by omega⟩ at equation
  have value := value_of_bounded_pair (radix := 256) (capacity := 256) (by decide) low high equation.symm
  exact ⟨by rw [value]; omega, value⟩

/-- Each actual selected write limb equals two bytes of the unchanged original lane rotation. -/
theorem theta_write_limb_rotation (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ThetaRhoCached.clockConstraints thetaRhoFixedTable
        else ThetaRho.clockConstraints thetaRhoFixedTable)) (column lane : Fin 5) (limb : Fin 4)
    (flags : ∀ selected : Fin 5, thetaColumnFlag cached w selected = if selected.val = column.val then 1 else 0) :
    (thetaLaneLimb cached true w ⟨lane.val, by omega⟩ limb).val =
      rotatedLaneByte (thetaXoredStateBytes cached w lane) (Call.rotations[column][lane]) ⟨2 * limb.val, by omega⟩ +
        256 * rotatedLaneByte (thetaXoredStateBytes cached w lane) (Call.rotations[column][lane])
          ⟨2 * limb.val + 1, by omega⟩ := by
  rw [(theta_write_limb_value cached w holds column lane limb flags).2,
    theta_output_byte_value cached w holds column lane ⟨2 * limb.val, by omega⟩ flags,
    theta_output_byte_value cached w holds column lane ⟨2 * limb.val + 1, by omega⟩ flags]

end Airbender.Keccak.Split.Native.Proofs
