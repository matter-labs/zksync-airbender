module
public import Proven.Compiler.WorkerConstraints.BlakeG.Source
public import Proven.Compiler.WorkerConstraints.BlakeG.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement16 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 37) (by change 37 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement17 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 38) (by change 38 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement18 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 39) (by change 39 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement19 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 0) (by change 0 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .blakeG 2 index := by
  apply (refinement20 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 1) (by change 1 < 42; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∀ values ∈ tuple2_001 physical, ∃ index, values = NativeWorkerSetup.rows .blakeG 2 index :=
  (all_cons (backwards16 physical logical agreement holds) (all_cons (backwards17 physical logical agreement holds) (all_cons (backwards18 physical logical agreement holds) (all_cons (backwards19 physical logical agreement holds) (all_cons (backwards20 physical logical agreement holds) (by intro value member; cases member))))))

end Airbender.Compiler.WorkerConstraints.BlakeG
