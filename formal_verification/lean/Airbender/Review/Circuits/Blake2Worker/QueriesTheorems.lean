import Airbender.Proofs.Blake2Worker.NativeQueryResults

namespace Airbender.Blake2Worker.Native
open Verification

/-- Complete local native acceptance on the actual worker pool derives all296
    lookup observations. Memory, processing/clock enforcement and protocol remain separate. -/
theorem lookup_effects {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (constraints Fixed.table)) : LookupEffects w := by
  exact QueryProofs.lookup_effects holds

end Airbender.Blake2Worker.Native
