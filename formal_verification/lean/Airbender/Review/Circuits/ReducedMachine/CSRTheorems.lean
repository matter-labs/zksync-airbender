import Airbender.Proofs.ReducedMachine.NativeCSRResult

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false
/-- Exact native CSR fixture, return and imported delegation request observables.
    The explicit local mask is separate from original decoding/execution. -/
theorem csr_native_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (csrMask : ZMod mersenne31Modulus)) : CSRNativeEffects w :=
  NativeCSRResultProofs.effects holds mask
end Airbender.ReducedMachine.Native
