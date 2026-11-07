import Airbender.Proofs.ReducedMachine.NativeBranchFields

namespace Airbender.ReducedMachine.Native
open Verification

/-- Local native branch routing, dummy port and shared remainder zero-test.
    Original branch decoding, condition/target meaning and execution are separate. -/
theorem branch_routing {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mask : w 12 = (branchMask : ZMod mersenne31Modulus)) : BranchRouting w := by
  exact NativeBranchFieldProofs.routing holds mask

end Airbender.ReducedMachine.Native
