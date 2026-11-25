module
public import Proven.UnifiedReduced.Proth120.ClockEquations

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Verification

theorem clock_advance : ClockAdvanceClaim := by
  intro setup w holds initial
  have row := holds_of_sublist holds (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  have times := holds_of_sublist holds (List.sublist_append_right (importedConstraints setup) importedConstraintsTimestampLookups)
  exact UnifiedReduced.Standard.clock_advance (profile := .proth120) (by decide) time_inverse
    (UnifiedReduced.Standard.Profile.clockSquare_correct .proth120) (UnifiedReduced.Standard.proth120_holds row) times initial

end Airbender.UnifiedReduced.Proth120
