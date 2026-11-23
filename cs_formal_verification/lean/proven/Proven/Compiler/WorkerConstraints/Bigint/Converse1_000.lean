module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.Compiler.WorkerConstraints.Bigint.Fields000
public import Proven.Compiler.WorkerConstraints.Bigint.Fields001
public import Proven.Compiler.WorkerConstraints.Bigint.Fields014

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement0 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 0) (by change 0 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement1 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 1) (by change 1 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement2 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 2) (by change 2 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement3 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 3) (by change 3 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement4 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 4) (by change 4 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement5 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 5) (by change 5 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement6 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 6) (by change 6 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement7 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 7) (by change 7 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement8 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 8) (by change 8 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement9 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 9) (by change 9 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement10 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 10) (by change 10 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement11 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 11) (by change 11 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement12 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 12) (by change 12 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement13 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 13) (by change 13 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement14 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 14) (by change 14 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards117 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand117.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement117 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 16) (by change 16 < 136; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse1_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ values ∈ tuple1_000 physical, ∃ index, values = NativeWorkerSetup.rows .bigint 1 index :=
  (all_cons (backwards0 physical logical agreement holds) (all_cons (backwards1 physical logical agreement holds) (all_cons (backwards2 physical logical agreement holds) (all_cons (backwards3 physical logical agreement holds) (all_cons (backwards4 physical logical agreement holds) (all_cons (backwards5 physical logical agreement holds) (all_cons (backwards6 physical logical agreement holds) (all_cons (backwards7 physical logical agreement holds) (all_cons (backwards8 physical logical agreement holds) (all_cons (backwards9 physical logical agreement holds) (all_cons (backwards10 physical logical agreement holds) (all_cons (backwards11 physical logical agreement holds) (all_cons (backwards12 physical logical agreement holds) (all_cons (backwards13 physical logical agreement holds) (all_cons (backwards14 physical logical agreement holds) (all_cons (backwards117 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
