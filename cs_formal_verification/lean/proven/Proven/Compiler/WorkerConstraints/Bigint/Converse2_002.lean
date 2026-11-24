module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.Compiler.WorkerConstraints.Bigint.Fields005
public import Proven.Compiler.WorkerConstraints.Bigint.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand47.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement47 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 127) (by change 127 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement48 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 128) (by change 128 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement49 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 129) (by change 129 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement50 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 130) (by change 130 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement51 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 131) (by change 131 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards52 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand52.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement52 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 132) (by change 132 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards53 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand53.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement53 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 133) (by change 133 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards54 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand54.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement54 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 32) (by change 32 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards55 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand55.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  apply (refinement55 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 33) (by change 33 < 136; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_002 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ values ∈ tuple2_002 physical, ∃ index, values = NativeWorkerSetup.rows .bigint 2 index :=
  (all_cons (backwards47 physical logical agreement holds) (all_cons (backwards48 physical logical agreement holds) (all_cons (backwards49 physical logical agreement holds) (all_cons (backwards50 physical logical agreement holds) (all_cons (backwards51 physical logical agreement holds) (all_cons (backwards52 physical logical agreement holds) (all_cons (backwards53 physical logical agreement holds) (all_cons (backwards54 physical logical agreement holds) (all_cons (backwards55 physical logical agreement holds) (by intro value member; cases member))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
