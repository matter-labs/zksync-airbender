module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.Compiler.WorkerConstraints.Bigint.Fields009
public import Proven.Compiler.WorkerConstraints.Bigint.Fields010

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards72 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand72.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement72 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 50) (by change 50 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards73 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand73.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement73 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 51) (by change 51 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards74 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand74.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement74 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 52) (by change 52 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards75 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand75.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement75 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 53) (by change 53 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards76 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand76.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement76 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 54) (by change 54 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards77 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand77.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement77 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 55) (by change 55 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards78 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand78.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement78 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 56) (by change 56 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards79 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand79.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement79 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 57) (by change 57 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards80 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand80.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement80 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 58) (by change 58 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards81 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand81.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement81 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 59) (by change 59 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards82 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand82.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement82 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 60) (by change 60 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards83 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand83.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement83 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 61) (by change 61 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards84 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand84.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement84 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 62) (by change 62 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards85 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand85.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement85 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 63) (by change 63 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards86 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand86.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement86 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 64) (by change 64 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards87 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand87.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement87 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 65) (by change 65 < 136; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ values ∈ tuple0_001 physical, ∃ index, values = NativeWorkerSetup.rows .bigint 0 index :=
  (all_cons (backwards72 physical logical agreement holds) (all_cons (backwards73 physical logical agreement holds) (all_cons (backwards74 physical logical agreement holds) (all_cons (backwards75 physical logical agreement holds) (all_cons (backwards76 physical logical agreement holds) (all_cons (backwards77 physical logical agreement holds) (all_cons (backwards78 physical logical agreement holds) (all_cons (backwards79 physical logical agreement holds) (all_cons (backwards80 physical logical agreement holds) (all_cons (backwards81 physical logical agreement holds) (all_cons (backwards82 physical logical agreement holds) (all_cons (backwards83 physical logical agreement holds) (all_cons (backwards84 physical logical agreement holds) (all_cons (backwards85 physical logical agreement holds) (all_cons (backwards86 physical logical agreement holds) (all_cons (backwards87 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
