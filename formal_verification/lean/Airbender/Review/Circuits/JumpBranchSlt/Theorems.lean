import Airbender.Review.Circuits.JumpBranchSlt.Model
import Airbender.Proofs.JumpBranchSlt.PC

namespace Airbender.JumpBranchSlt

/-- Every native row constraint and fixed query derives exact control/cleanup
    observables. This claim does not assert original Sail instruction execution. -/
theorem native_fixed_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    FixedEffects w :=
  Proofs.fixed_effects holds

/-- Supported native opcode masks derive both outgoing PC limb bounds from
    native equations/lookups. Binding the mask to public decoding is separate. -/
theorem native_pc_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mask : (w 12).val ∈ [1, 2, 4, 8, 16]) :
    (w 13).val < 65536 ∧ (w 14).val < 65536 :=
  Proofs.pc_bounds holds mask

end Airbender.JumpBranchSlt
