import Tests.MulDiv
import Airbender.Proofs.MulDiv.Trace

namespace Tests.MulDivTimestamp
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- DIVU/REMU by zero; rd aliases rs1. Native clocks include the source refresh
-- before the destination write, and the 19-bit low-clock rollover.
def assignment (remainder rollover : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 2 then (if rollover then 524284 else 4)
  else if i = 3 || i = 19 || i = 23 || i = 31 then (if rollover then 7 else 0)
  else if i = 16 then (if rollover then 0 else 8)
  else if i = 17 then (if rollover then 8 else 0)
  else if i = 26 then 7 else if i = 27 then 2
  else if i = 30 then (if rollover then 524284 else 4)
  else if i = 65 || i = 66 || i = 67 then 1
  else MulDiv.row remainder i

theorem constraints (remainder rollover : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment remainder rollover)) Airbender.MulDiv.clockConstraints := by
  apply Verification.holds_append (left := Airbender.MulDiv.importedConstraints)
    (right := Airbender.MulDiv.importedConstraintsTimestampLookups)
  · have core := MulDiv.satisfies remainder
    cases remainder <;> cases rollover <;>
      simpa [Airbender.MulDiv.importedConstraints, FlatOperation.ConstraintsHoldFlat,
        Lookup.Contains, Vector.map, Expression.eval, Verification.environment, assignment, MulDiv.row,
        Verification.range16, Verification.range13, Verification.pairLookup,
        show (4 : ZMod babyBearModulus) + 4 + -8 = 0 by decide,
        show (14745600 : ZMod babyBearModulus) * (524284 + 4) * (524284 + 4) +
          3840 * (524284 + 4) = 0 by decide,
        show (8 : ZMod babyBearModulus) + -7 + 3840 * (524284 + 4) = 0 by decide] using core
  · cases remainder <;> cases rollover <;>
      simp [Airbender.MulDiv.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment, MulDiv.row]
    all_goals decide

theorem native_clocks (remainder rollover : Bool) :
    ClockEffects Airbender.MulDiv.importedConstraintsTraceColumns (assignment remainder rollover) := by
  apply Airbender.MulDiv.Proofs.clocks (by decide) (by decide) (constraints remainder rollover)
  constructor
  · cases remainder <;> cases rollover <;> constructor <;> decide
  · cases remainder <;> cases rollover <;> decide
  · intro port member
    simp [Airbender.MulDiv.importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> cases remainder <;> cases rollover <;> constructor <;> decide

end Tests.MulDivTimestamp
