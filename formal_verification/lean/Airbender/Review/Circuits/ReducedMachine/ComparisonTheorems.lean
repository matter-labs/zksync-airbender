import Airbender.Proofs.ReducedMachine.NativeComparisonResult

namespace Airbender.ReducedMachine.Native
open Verification
set_option autoImplicit false

/-- Actual monolithic comparison routing, Boolean candidate, masked write and
    default PC. Original decoding supplies the explicit mask and raw funct3. -/
theorem comparison_effects {w : Nat → ZMod mersenne31Modulus}
    (accepted : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (useRegister signed : Bool)
    (mask : w 12 = (comparisonMask useRegister : ZMod mersenne31Modulus))
    (tag : w 11 = (if signed then 2 else 3)) : ComparisonEffects w useRegister :=
  NativeComparisonResultProofs.effects accepted useRegister signed mask tag

end Airbender.ReducedMachine.Native
