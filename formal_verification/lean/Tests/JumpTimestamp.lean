import Airbender.Review.JumpBranchSlt.Theorems

namespace Tests.JumpTimestamp
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

-- JAL x1,-4 at PC zero. Clock rollover crosses a 19-bit limb while the
-- architectural target is unchanged; every previous-write clock is earlier.
private def assignment (rollover : Bool) : Nat → ZMod babyBearModulus
  | 2 => if rollover then 524284 else 4
  | 3 | 21 | 25 | 33 => if rollover then 7 else 0
  | 4 | 7 | 11 | 49 | 50 | 51 => 1
  | 8 | 16 | 36 => 65532
  | 9 | 17 => 65535
  | 18 => if rollover then 0 else 8
  | 19 => if rollover then 8 else 0
  | 30 | 34 | 47 => 4
  | _ => 0

private theorem constraints (rollover : Bool) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment rollover))
      JumpBranchSlt.clockConstraints := by
  cases rollover <;>
    simp [JumpBranchSlt.clockConstraints, JumpBranchSlt.importedConstraints,
      JumpBranchSlt.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains; decide)
    | (apply Proofs.range_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 65536,
        ((0, 0) : fieldPair (ZMod babyBearModulus)) =
          ((i.val : ZMod babyBearModulus), ((i.val / 32768 : Nat) : ZMod babyBearModulus))
       exact ⟨0, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 131072,
        ((4, 0) : fieldPair (ZMod babyBearModulus)) =
          ((i.val : ZMod babyBearModulus), ((if i.val = 0 then 1 else 0 : Nat) : ZMod babyBearModulus))
       exact ⟨4, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 4194304,
        ((0, 0) : fieldPair (ZMod babyBearModulus)) =
          ((i.val : ZMod babyBearModulus), (Verification.conditionalValue i.val : ZMod babyBearModulus))
       exact ⟨0, rfl⟩)
    | (with_unfolding_all change ∃ i : Fin 65536,
        ((65532, 0, 65532) : fieldTriple (ZMod babyBearModulus)) =
          ((i.val : ZMod babyBearModulus), ((i.val / 2 % 2 : Nat) : ZMod babyBearModulus),
            ((i.val - i.val % 4 : Nat) : ZMod babyBearModulus))
       exact ⟨65532, rfl⟩)

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
