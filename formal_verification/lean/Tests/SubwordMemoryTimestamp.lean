import Tests.SubwordMemory
import Airbender.Proofs.SubwordMemory.Trace
import Airbender.Review.Helpers.Tables.Subword

namespace Tests.SubwordMemoryTimestamp
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

-- LBU x2,0(x1), where x1 points to 0x00400001, with independent
-- register/RAM ports. Exercise ordinary clocks and the 19-bit rollover.
def assignment (rollover : Bool) (i : Nat) : ZMod babyBearModulus :=
  if i = 2 then (if rollover then 524284 else 4)
  else if i = 3 then (if rollover then 7 else 0)
  else if i = 15 then (if rollover then 0 else 8)
  else if i = 16 then (if rollover then 8 else 0)
  else if i = 62 || i = 63 || i = 64 then 1
  else SubwordMemory.row i

theorem constraints (rollover : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment rollover)) (Airbender.SubwordMemory.clockConstraints (Verification.subwordTable (fun _ => 0))) := by
  apply Verification.holds_append (left := Airbender.SubwordMemory.importedConstraints (Verification.subwordTable (fun _ => 0)))
    (right := Airbender.SubwordMemory.importedConstraintsTimestampLookups)
  · have core := SubwordMemory.satisfies_setup
    cases rollover <;>
      simpa [Airbender.SubwordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
        Lookup.Contains, Vector.map, Expression.eval, Verification.environment, assignment, SubwordMemory.row, Verification.range16,
        show (4 : ZMod babyBearModulus) + 4 + -8 = 0 by decide,
        show (14745600 : ZMod babyBearModulus) * (524284 + 4) * (524284 + 4) +
          3840 * (524284 + 4) = 0 by decide,
        show (8 : ZMod babyBearModulus) + -7 + 3840 * (524284 + 4) = 0 by decide] using core
  · cases rollover <;>
      simp [Airbender.SubwordMemory.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment, SubwordMemory.row]
    all_goals decide

theorem native_clocks (rollover : Bool) :
    ClockEffects Airbender.SubwordMemory.importedConstraintsTraceColumns (assignment rollover) := by
  apply Airbender.SubwordMemory.Proofs.clocks (by decide) (by decide) (constraints rollover)
  constructor
  · cases rollover <;> constructor <;> decide
  · cases rollover <;> decide
  · intro port member
    simp [Airbender.SubwordMemory.importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> cases rollover <;> constructor <;> decide

end Tests.SubwordMemoryTimestamp
