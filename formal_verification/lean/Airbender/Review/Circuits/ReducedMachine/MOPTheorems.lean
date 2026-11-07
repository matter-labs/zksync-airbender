import Airbender.Proofs.ReducedMachine.NativeMOPResult

namespace Airbender.ReducedMachine.Native
set_option autoImplicit false

/-- Actual native MOP ports, field operation, canonical result, masked write and
    default-PC selection follow the unchanged117-equation artifact. The explicit
    mask is an internal decoder interface, not original Sail execution evidence. -/
theorem mop_arithmetic {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (mode : MOPMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) : MOPNativeEffects w mode :=
  NativeMOPResultProofs.effects holds mode mask

end Airbender.ReducedMachine.Native
