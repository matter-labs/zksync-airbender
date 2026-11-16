module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.Compiler.WorkerConstraints.Bigint.Fields011
public import Proven.Compiler.WorkerConstraints.Bigint.Fields012

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards88 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand88.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement88 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 66) (by change 66 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards89 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand89.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement89 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 67) (by change 67 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards90 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand90.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement90 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 68) (by change 68 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards91 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand91.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement91 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 69) (by change 69 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards92 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand92.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement92 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 70) (by change 70 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards93 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand93.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement93 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 71) (by change 71 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards94 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand94.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement94 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 72) (by change 72 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards95 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand95.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement95 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 73) (by change 73 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards96 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand96.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement96 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 74) (by change 74 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards97 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand97.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement97 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 75) (by change 75 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards98 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand98.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement98 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 76) (by change 76 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards99 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand99.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement99 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 77) (by change 77 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards100 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand100.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement100 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 78) (by change 78 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards101 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand101.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement101 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 79) (by change 79 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards102 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand102.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement102 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 80) (by change 80 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards103 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand103.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement103 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 81) (by change 81 < 136; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_002 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ values ∈ tuple0_002 physical, ∃ index, values = NativeWorkerSetup.rows .bigint 0 index :=
  (all_cons (backwards88 physical logical agreement holds) (all_cons (backwards89 physical logical agreement holds) (all_cons (backwards90 physical logical agreement holds) (all_cons (backwards91 physical logical agreement holds) (all_cons (backwards92 physical logical agreement holds) (all_cons (backwards93 physical logical agreement holds) (all_cons (backwards94 physical logical agreement holds) (all_cons (backwards95 physical logical agreement holds) (all_cons (backwards96 physical logical agreement holds) (all_cons (backwards97 physical logical agreement holds) (all_cons (backwards98 physical logical agreement holds) (all_cons (backwards99 physical logical agreement holds) (all_cons (backwards100 physical logical agreement holds) (all_cons (backwards101 physical logical agreement holds) (all_cons (backwards102 physical logical agreement holds) (all_cons (backwards103 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
