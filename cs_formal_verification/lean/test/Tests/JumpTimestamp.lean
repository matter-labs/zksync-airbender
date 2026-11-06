import Slop.JumpBranchSlt.Claims
import Slop.JumpBranchSlt.Completeness.Witness

namespace Tests.JumpTimestamp
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

-- JAL x1,-4 at PC zero. Clock rollover crosses a 19-bit limb while the
-- architectural target is unchanged; every previous-write clock is earlier.
def assignment (rollover : Bool) : Nat → ZMod babyBearModulus
  | 2 => if rollover then 524284 else 4
  | 3 | 21 | 25 | 33 => if rollover then 7 else 0
  | 4 | 7 | 11 | 49 | 50 | 51 => 1
  | 8 | 16 | 36 => 65532
  | 9 | 17 => 65535
  | 18 => if rollover then 0 else 8
  | 19 => if rollover then 8 else 0
  | 30 | 34 | 47 => 4
  | _ => 0

/-- The honest inputs `assignment` is built from; every previous clock is `(0, tsHi)`. -/
def witness (rollover : Bool) : JumpBranchSlt.Completeness.Inputs where
  sel := 0
  rdZero := false
  funct3 := 0
  rs1 := 0
  rs2 := 0
  rd := 1
  pcLo := 0
  pcHi := 0
  aLo := 0
  aHi := 0
  bLo := 0
  bHi := 0
  immLo := 65532
  immHi := 65535
  oldLo := 0
  oldHi := 0
  tsLo := if rollover then 524284 else 4
  tsHi := if rollover then 7 else 0
  prev0Lo := 0
  prev0Hi := if rollover then 7 else 0
  prev1Lo := 0
  prev1Hi := if rollover then 7 else 0
  prev2Lo := 0
  prev2Hi := if rollover then 7 else 0
  borrow0 := 1
  borrow1 := 1
  borrow2 := 1

theorem constraints (rollover : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment rollover))
      JumpBranchSlt.clockConstraints :=
  JumpBranchSlt.Completeness.clock_complete_of_agree (witness rollover)
    (by cases rollover <;> constructor <;> decide) (by cases rollover <;> constructor <;> decide)
    (by cases rollover <;> decide)

private theorem inputs (rollover : Bool) :
    ClockInputs JumpBranchSlt.importedConstraintsTraceColumns (assignment rollover) := by
  refine ⟨?_, ?_, ?_⟩
  · cases rollover <;> constructor <;> decide
  · cases rollover <;> decide
  · intro port member
    simp [JumpBranchSlt.importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> cases rollover <;> constructor <;> decide

/-- Both ordinary advancement and low-limb rollover satisfy the full imported
    clock relation, including all three prior-write comparisons. -/
theorem checked_clocks (rollover : Bool) :
    ClockEffects JumpBranchSlt.importedConstraintsTraceColumns (assignment rollover) :=
  JumpBranchSlt.clocks (constraints rollover) (inputs rollover)

/-- Replacing the first borrow bit by zero keeps it Boolean but violates the
    actual timestamp lookup. The artifact, rather than a supplied order, rejects it. -/
theorem incorrect_borrow_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun i => if i = 49 then 0 else assignment false i))
      JumpBranchSlt.clockConstraints := by
  intro accepted
  have timestamps := Verification.holds_of_sublist accepted
    (List.sublist_append_right JumpBranchSlt.importedConstraints
      JumpBranchSlt.importedConstraintsTimestampLookups)
  have lower := Proofs.range_bound (Verification.lookup_of_holds timestamps
    ⟨2, by simp [JumpBranchSlt.importedConstraintsTimestampLookups, FlatOperation.lookups]⟩)
  have impossible : ((-4 : ZMod babyBearModulus)).val < timestampBase := by
    simpa [Expression.eval, Verification.environment, assignment] using lower
  contradiction

end Tests.JumpTimestamp
