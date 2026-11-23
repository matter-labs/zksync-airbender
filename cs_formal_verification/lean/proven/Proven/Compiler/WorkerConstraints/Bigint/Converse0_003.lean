module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.Compiler.WorkerConstraints.Bigint.Fields013
public import Proven.Compiler.WorkerConstraints.Bigint.Fields014

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards104 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand104.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement104 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 82) (by change 82 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards105 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand105.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement105 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 83) (by change 83 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards106 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand106.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement106 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 84) (by change 84 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards107 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand107.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement107 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 85) (by change 85 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards108 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand108.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement108 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 86) (by change 86 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards109 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand109.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement109 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 87) (by change 87 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards110 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand110.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement110 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 88) (by change 88 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards111 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand111.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement111 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 89) (by change 89 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards112 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand112.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement112 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 90) (by change 90 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards113 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand113.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement113 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 91) (by change 91 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards114 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand114.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement114 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 92) (by change 92 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards115 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand115.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement115 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 93) (by change 93 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards116 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand116.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement116 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 94) (by change 94 < 136; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_003 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ values ∈ tuple0_003 physical, ∃ index, values = NativeWorkerSetup.rows .bigint 0 index :=
  (all_cons (backwards104 physical logical agreement holds) (all_cons (backwards105 physical logical agreement holds) (all_cons (backwards106 physical logical agreement holds) (all_cons (backwards107 physical logical agreement holds) (all_cons (backwards108 physical logical agreement holds) (all_cons (backwards109 physical logical agreement holds) (all_cons (backwards110 physical logical agreement holds) (all_cons (backwards111 physical logical agreement holds) (all_cons (backwards112 physical logical agreement holds) (all_cons (backwards113 physical logical agreement holds) (all_cons (backwards114 physical logical agreement holds) (all_cons (backwards115 physical logical agreement holds) (all_cons (backwards116 physical logical agreement holds) (by intro value member; cases member))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
