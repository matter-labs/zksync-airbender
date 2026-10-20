import Tests.ShiftBinop
import Slop.ShiftBinop.Trace

namespace Tests.ShiftBinopTimestamp
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- XOR x1,x0,x0. Both byte-based source ports alias x0, so the second
-- reads the first refresh timestamp. Cover the 19-bit low-clock rollover.
def assignment (rollover : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 2 then (if rollover then 524284 else 4)
  else if i = 3 || i = 18 || i = 24 || i = 34 then (if rollover then 7 else 0)
  else if i = 15 then (if rollover then 0 else 8)
  else if i = 16 then (if rollover then 8 else 0)
  else if i = 23 then (if rollover then 524284 else 4)
  else if i = 92 || i = 93 || i = 94 then 1
  else ShiftBinop.row false i

theorem constraints (rollover : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment rollover)) Airbender.ShiftBinop.clockConstraints := by
  apply Verification.holds_append (left := Airbender.ShiftBinop.importedConstraints)
    (right := Airbender.ShiftBinop.importedConstraintsTimestampLookups)
  · have core := ShiftBinop.satisfies
    cases rollover <;>
      simpa [Airbender.ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat,
        Lookup.Contains, Vector.map, Expression.eval, Verification.environment, assignment, ShiftBinop.row,
        Verification.shiftBinopLookup, Verification.range16,
        show (4 : ZMod babyBearModulus) + 4 + -8 = 0 by decide,
        show (14745600 : ZMod babyBearModulus) * (524284 + 4) * (524284 + 4) +
          3840 * (524284 + 4) = 0 by decide,
        show (8 : ZMod babyBearModulus) + -7 + 3840 * (524284 + 4) = 0 by decide] using core
  · cases rollover <;>
      simp [Airbender.ShiftBinop.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment, ShiftBinop.row]
    all_goals decide

theorem native_clocks (rollover : Bool) :
    ClockEffects Airbender.ShiftBinop.importedConstraintsTraceColumns (assignment rollover) := by
  apply Airbender.ShiftBinop.Proofs.clocks (by decide) (by decide) (constraints rollover)
  constructor
  · cases rollover <;> constructor <;> decide
  · cases rollover <;> decide
  · intro port member
    simp [Airbender.ShiftBinop.importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> cases rollover <;> constructor <;> decide

end Tests.ShiftBinopTimestamp
