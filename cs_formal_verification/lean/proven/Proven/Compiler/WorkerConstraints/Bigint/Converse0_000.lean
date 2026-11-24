module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.Compiler.WorkerConstraints.Bigint.Fields007
public import Proven.Compiler.WorkerConstraints.Bigint.Fields008

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards56 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand56.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement56 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 34) (by change 34 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards57 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand57.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement57 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 35) (by change 35 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards58 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand58.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement58 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 36) (by change 36 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards59 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand59.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement59 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 37) (by change 37 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards60 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand60.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement60 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 38) (by change 38 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards61 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand61.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement61 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 39) (by change 39 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards62 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand62.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement62 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 40) (by change 40 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards63 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand63.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement63 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 41) (by change 41 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards64 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand64.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement64 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 42) (by change 42 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards65 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand65.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement65 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 43) (by change 43 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards66 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand66.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement66 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 44) (by change 44 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards67 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand67.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement67 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 45) (by change 45 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards68 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand68.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement68 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 46) (by change 46 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards69 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand69.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement69 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 47) (by change 47 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards70 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand70.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement70 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 48) (by change 48 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards71 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand71.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  apply (refinement71 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 49) (by change 49 < 136; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ values ∈ tuple0_000 physical, ∃ index, values = NativeWorkerSetup.rows .bigint 0 index :=
  (all_cons (backwards56 physical logical agreement holds) (all_cons (backwards57 physical logical agreement holds) (all_cons (backwards58 physical logical agreement holds) (all_cons (backwards59 physical logical agreement holds) (all_cons (backwards60 physical logical agreement holds) (all_cons (backwards61 physical logical agreement holds) (all_cons (backwards62 physical logical agreement holds) (all_cons (backwards63 physical logical agreement holds) (all_cons (backwards64 physical logical agreement holds) (all_cons (backwards65 physical logical agreement holds) (all_cons (backwards66 physical logical agreement holds) (all_cons (backwards67 physical logical agreement holds) (all_cons (backwards68 physical logical agreement holds) (all_cons (backwards69 physical logical agreement holds) (all_cons (backwards70 physical logical agreement holds) (all_cons (backwards71 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
