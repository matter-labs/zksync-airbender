module
public import Proven.Compiler.WorkerConstraints.BlakeG.Source
public import Proven.Compiler.WorkerConstraints.BlakeG.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields002
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields003
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields004

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement21 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 2) (by change 2 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement22 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 3) (by change 3 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement23 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 4) (by change 4 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement24 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 5) (by change 5 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement25 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 6) (by change 6 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement26 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 7) (by change 7 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement27 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 8) (by change 8 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement28 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 9) (by change 9 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement29 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 10) (by change 10 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement30 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 11) (by change 11 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement31 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 12) (by change 12 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement32 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 13) (by change 13 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement33 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 14) (by change 14 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement34 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 15) (by change 15 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement35 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 16) (by change 16 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement36 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 17) (by change 17 < 42; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∀ values ∈ tuple0_000 physical, ∃ index, values = NativeWorkerSetup.rows .blakeG 0 index :=
  (all_cons (backwards21 physical logical agreement holds) (all_cons (backwards22 physical logical agreement holds) (all_cons (backwards23 physical logical agreement holds) (all_cons (backwards24 physical logical agreement holds) (all_cons (backwards25 physical logical agreement holds) (all_cons (backwards26 physical logical agreement holds) (all_cons (backwards27 physical logical agreement holds) (all_cons (backwards28 physical logical agreement holds) (all_cons (backwards29 physical logical agreement holds) (all_cons (backwards30 physical logical agreement holds) (all_cons (backwards31 physical logical agreement holds) (all_cons (backwards32 physical logical agreement holds) (all_cons (backwards33 physical logical agreement holds) (all_cons (backwards34 physical logical agreement holds) (all_cons (backwards35 physical logical agreement holds) (all_cons (backwards36 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeG
