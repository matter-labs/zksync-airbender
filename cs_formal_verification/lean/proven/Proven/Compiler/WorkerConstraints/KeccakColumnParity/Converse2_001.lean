module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Source
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields002
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields003
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement16 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 39) (by change 39 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement17 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 40) (by change 40 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement18 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 41) (by change 41 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement19 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 42) (by change 42 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement20 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 43) (by change 43 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement21 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 44) (by change 44 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement22 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 45) (by change 45 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement23 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 46) (by change 46 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement24 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 47) (by change 47 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement25 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 48) (by change 48 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement26 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 49) (by change 49 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement27 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 50) (by change 50 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement28 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 51) (by change 51 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  apply (refinement50 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 0) (by change 0 < 53; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∀ values ∈ tuple2_001 physical, ∃ index, values = NativeWorkerSetup.rows .columnParity 2 index :=
  (all_cons (backwards16 physical logical agreement holds) (all_cons (backwards17 physical logical agreement holds) (all_cons (backwards18 physical logical agreement holds) (all_cons (backwards19 physical logical agreement holds) (all_cons (backwards20 physical logical agreement holds) (all_cons (backwards21 physical logical agreement holds) (all_cons (backwards22 physical logical agreement holds) (all_cons (backwards23 physical logical agreement holds) (all_cons (backwards24 physical logical agreement holds) (all_cons (backwards25 physical logical agreement holds) (all_cons (backwards26 physical logical agreement holds) (all_cons (backwards27 physical logical agreement holds) (all_cons (backwards28 physical logical agreement holds) (all_cons (backwards50 physical logical agreement holds) (by intro value member; cases member)))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
