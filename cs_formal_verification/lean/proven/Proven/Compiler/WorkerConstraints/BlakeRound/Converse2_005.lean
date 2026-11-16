module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields010
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields011

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards80 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand80.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement80 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 274) (by change 274 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards81 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand81.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement81 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 275) (by change 275 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards82 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand82.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement82 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 276) (by change 276 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards83 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand83.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement83 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 277) (by change 277 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards84 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand84.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement84 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 278) (by change 278 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards85 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand85.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement85 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 279) (by change 279 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards86 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand86.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement86 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 280) (by change 280 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards87 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand87.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement87 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 0) (by change 0 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards88 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand88.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement88 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 1) (by change 1 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_005 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple2_005 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 2 index :=
  (all_cons (backwards80 physical logical agreement holds) (all_cons (backwards81 physical logical agreement holds) (all_cons (backwards82 physical logical agreement holds) (all_cons (backwards83 physical logical agreement holds) (all_cons (backwards84 physical logical agreement holds) (all_cons (backwards85 physical logical agreement holds) (all_cons (backwards86 physical logical agreement holds) (all_cons (backwards87 physical logical agreement holds) (all_cons (backwards88 physical logical agreement holds) (by intro value member; cases member))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
