module
public import Tests.MulDiv
public import Slop.MulDiv.Trace
public import Slop.Verification.StaticLookup
public import Mathlib.Tactic.IntervalCases
import all Init.Data.Array.Basic -- until Lean 4.35 exposes Array/Vector ofFn/DecidableEq (lean4#14989, #14988, #14270)

@[expose] public section

namespace Tests.MulDivTimestamp
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

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
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · cases remainder <;> cases rollover <;> decide
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 16 := by simpa only [Airbender.MulDiv.lookup_count] using bound
      interval_cases i
      all_goals first
        | exact Verification.range16_contains (by cases remainder <;> cases rollover <;> decide)
        | exact Verification.range13_contains (by cases remainder <;> cases rollover <;> decide)
        | exact Verification.static_lookup_contains _ _ _ (by cases remainder <;> cases rollover <;> decide +kernel)
            (by cases remainder <;> cases rollover <;> decide +kernel)
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [Airbender.MulDiv.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [Airbender.MulDiv.timestamp_count] using bound
      interval_cases i
      all_goals exact Proofs.range_contains (by cases remainder <;> cases rollover <;> decide)

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
