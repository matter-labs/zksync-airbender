module
public import Proven.Compiler.WorkerConstraints.BlakeG.Source
public import Proven.Compiler.WorkerConstraints.BlakeG.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields000
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement0 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 21) (by change 21 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement1 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 22) (by change 22 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement2 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 23) (by change 23 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement3 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 24) (by change 24 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement4 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 25) (by change 25 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement5 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 26) (by change 26 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement6 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 27) (by change 27 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement7 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 28) (by change 28 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement8 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 29) (by change 29 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement9 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 30) (by change 30 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement10 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 31) (by change 31 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement11 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 32) (by change 32 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement12 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 33) (by change 33 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement13 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 34) (by change 34 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement14 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 35) (by change 35 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement15 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 36) (by change 36 < 42; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∀ values ∈ tuple2_000 physical, ∃ index, values = NativeWorkerSetup.rows .blakeG 2 index :=
  (all_cons (backwards0 physical logical agreement holds) (all_cons (backwards1 physical logical agreement holds) (all_cons (backwards2 physical logical agreement holds) (all_cons (backwards3 physical logical agreement holds) (all_cons (backwards4 physical logical agreement holds) (all_cons (backwards5 physical logical agreement holds) (all_cons (backwards6 physical logical agreement holds) (all_cons (backwards7 physical logical agreement holds) (all_cons (backwards8 physical logical agreement holds) (all_cons (backwards9 physical logical agreement holds) (all_cons (backwards10 physical logical agreement holds) (all_cons (backwards11 physical logical agreement holds) (all_cons (backwards12 physical logical agreement holds) (all_cons (backwards13 physical logical agreement holds) (all_cons (backwards14 physical logical agreement holds) (all_cons (backwards15 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeG
