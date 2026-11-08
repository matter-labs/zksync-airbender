module
public import Human.Circuits.UnifiedReduced.Delegation
public import Human.Helpers.Delegation.Schedule

@[expose] public section

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Read the unified artifact's caller selector. Original public decoding below
    checks its meaning; this filter supplies no instruction or worker result. -/
def Selected (w : Nat → ZMod p) : Prop := w importedConstraintsDecoderColumns.flags[7] = 1
instance (w : Nat → ZMod p) : Decidable (Selected w) := inferInstanceAs
  (Decidable (w importedConstraintsDecoderColumns.flags[7] = 1))

end Airbender.UnifiedReduced.Caller
