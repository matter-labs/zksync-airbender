import Airbender.Review.Circuits.JumpBranchSlt.Model
import Airbender.Proofs.JumpBranchSlt.Queries

namespace Airbender.JumpBranchSlt

/-- Every native row constraint and fixed query derives exact control/cleanup
    observables. This claim does not assert original Sail instruction execution. -/
theorem native_fixed_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    FixedEffects w :=
  Proofs.fixed_effects holds

end Airbender.JumpBranchSlt
