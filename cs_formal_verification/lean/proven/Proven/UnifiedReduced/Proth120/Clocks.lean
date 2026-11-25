module
public import Proven.UnifiedReduced.Proth120.ClockEquations

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Verification
set_option maxRecDepth 8192

theorem clock_accesses {setup} {w : Nat → ZMod proth120Modulus}
    (h : FlatOperation.ConstraintsHoldFlat (environment w) (clockConstraints setup))
    (inputs : ClockInputs importedConstraintsTraceColumns w) : ClockEffects importedConstraintsTraceColumns w := by
  have core := holds_of_sublist h (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  have times := holds_of_sublist h (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
  exact UnifiedReduced.Standard.clock_accesses (profile := .proth120) (by decide) time_inverse
    (UnifiedReduced.Standard.Profile.clockSquare_correct .proth120) (UnifiedReduced.Standard.proth120_holds core) times inputs

end Airbender.UnifiedReduced.Proth120
