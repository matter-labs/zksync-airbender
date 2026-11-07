import Airbender.Proofs.ReducedMachine.NativeRuntimeCSRResult

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
/-- Selected local CSR effects on the explicit full runtime-CSR pool with the
    retained ROM fixture. No public decoding, caller stream or worker execution. -/
theorem runtime_csr_native_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints NativeRuntimePool.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) : CSRRuntimeEffects w :=
  NativeRuntimeCSRResultProofs.effects holds mask
end Airbender.ReducedMachine.Native
