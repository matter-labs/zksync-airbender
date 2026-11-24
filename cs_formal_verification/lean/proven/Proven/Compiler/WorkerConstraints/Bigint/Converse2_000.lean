module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.Compiler.WorkerConstraints.Bigint.Fields001
public import Proven.Compiler.WorkerConstraints.Bigint.Fields002
public import Proven.Compiler.WorkerConstraints.Bigint.Fields003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement15 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 95) (by change 95 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement16 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 96) (by change 96 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement17 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 97) (by change 97 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement18 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 98) (by change 98 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement19 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 99) (by change 99 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement20 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 100) (by change 100 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement21 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 101) (by change 101 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement22 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 102) (by change 102 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement23 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 103) (by change 103 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement24 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 104) (by change 104 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement25 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 105) (by change 105 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement26 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 106) (by change 106 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement27 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 107) (by change 107 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement28 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 108) (by change 108 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement29 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 109) (by change 109 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement30 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 110) (by change 110 < 136; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ values ∈ tuple2_000 physical, ∃ index, values = NativeWorkerSetup.rows .bigint 2 index :=
  (all_cons (backwards15 physical logical agreement holds) (all_cons (backwards16 physical logical agreement holds) (all_cons (backwards17 physical logical agreement holds) (all_cons (backwards18 physical logical agreement holds) (all_cons (backwards19 physical logical agreement holds) (all_cons (backwards20 physical logical agreement holds) (all_cons (backwards21 physical logical agreement holds) (all_cons (backwards22 physical logical agreement holds) (all_cons (backwards23 physical logical agreement holds) (all_cons (backwards24 physical logical agreement holds) (all_cons (backwards25 physical logical agreement holds) (all_cons (backwards26 physical logical agreement holds) (all_cons (backwards27 physical logical agreement holds) (all_cons (backwards28 physical logical agreement holds) (all_cons (backwards29 physical logical agreement holds) (all_cons (backwards30 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
