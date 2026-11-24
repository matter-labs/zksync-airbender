module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.Compiler.WorkerConstraints.Bigint.Fields003
public import Proven.Compiler.WorkerConstraints.Bigint.Fields004
public import Proven.Compiler.WorkerConstraints.Bigint.Fields005

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement31 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 111) (by change 111 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement32 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 112) (by change 112 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement33 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 113) (by change 113 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement34 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 114) (by change 114 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement35 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 115) (by change 115 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement36 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 116) (by change 116 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement37 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 117) (by change 117 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement38 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 118) (by change 118 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement39 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 119) (by change 119 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand40.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement40 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 120) (by change 120 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand41.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement41 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 121) (by change 121 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand42.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement42 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 122) (by change 122 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand43.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement43 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 123) (by change 123 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand44.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement44 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 124) (by change 124 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand45.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement45 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 125) (by change 125 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand46.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement46 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 126) (by change 126 < 136; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ values ∈ tuple2_001 physical, ∃ index, values = NativeWorkerSetup.rows .bigint 2 index :=
  (all_cons (backwards31 physical logical agreement holds) (all_cons (backwards32 physical logical agreement holds) (all_cons (backwards33 physical logical agreement holds) (all_cons (backwards34 physical logical agreement holds) (all_cons (backwards35 physical logical agreement holds) (all_cons (backwards36 physical logical agreement holds) (all_cons (backwards37 physical logical agreement holds) (all_cons (backwards38 physical logical agreement holds) (all_cons (backwards39 physical logical agreement holds) (all_cons (backwards40 physical logical agreement holds) (all_cons (backwards41 physical logical agreement holds) (all_cons (backwards42 physical logical agreement holds) (all_cons (backwards43 physical logical agreement holds) (all_cons (backwards44 physical logical agreement holds) (all_cons (backwards45 physical logical agreement holds) (all_cons (backwards46 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
