import Airbender.Proofs.Blake2Worker.NativeControl

namespace Airbender.Blake2Worker.Native
open Verification

/-- All actual local worker constraints imply the control flag bounds and
    x12 low clearing. This does not claim valid controls or worker execution. -/
theorem control_effects {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints setup)) : ControlEffects w := by
  exact NativeProofs.effects holds

end Airbender.Blake2Worker.Native
