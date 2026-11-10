module
public import Slop.Final.Helpers.Context.PCState.Theorems
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Core.BabyBearPrime
public import Slop.AddSub.Selectors
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Product
public import Human.Circuits.MulDiv.Operation
public import Slop.MulDiv.Values
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.Values
public import Slop.Trace.CompositionCore
public import Slop.Trace.Family.Values
public import Slop.Trace.Pooled
public import Slop.Trace.RowContext
public import Slop.CleanCore.Circuit.Operations
public import Slop.Defs.Helpers.Context.Columns

@[expose] public section

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

theorem inputs (rollover : Bool) :
    ClockInputs JumpBranchSlt.importedConstraintsTraceColumns (assignment rollover) := by
  refine ⟨?_, ?_, ?_⟩
  · cases rollover <;> constructor <;> decide
  · cases rollover <;> decide
  · intro port member
    simp [JumpBranchSlt.importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> cases rollover <;> constructor <;> decide

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
