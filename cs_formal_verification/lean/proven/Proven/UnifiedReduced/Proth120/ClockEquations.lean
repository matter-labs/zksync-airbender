module
public import Human.Circuits.UnifiedReduced.Proth120Clock
public import Proven.UnifiedReduced.Standard.Clocks

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Verification
open Airbender.UnifiedReduced.Standard (Profile)
set_option maxRecDepth 8192

abbrev timeInverse : ZMod proth120Modulus := Profile.proth120.clockInv

theorem time_inverse : timeInverse * 524288 = 1 := Profile.clockInv_correct .proth120

theorem clock_equations {setup} {w : Nat → ZMod proth120Modulus}
    (row : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup)) :
    ∃ c : Nat, c ≤ 1 ∧ w 2 + 4 = w 32 + 524288 * c ∧ w 3 + c = w 33 := by
  exact UnifiedReduced.Standard.clock_equations (profile := .proth120) time_inverse (Profile.clockSquare_correct .proth120)
    (UnifiedReduced.Standard.proth120_holds row)

theorem final_clock_bound {w : Nat → ZMod proth120Modulus}
    (times : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraintsTimestampLookups) :
    (decodeTimestamp w importedConstraintsTraceColumns.finalTime).Bounded := UnifiedReduced.Standard.final_clock_bound times

end Airbender.UnifiedReduced.Proth120
