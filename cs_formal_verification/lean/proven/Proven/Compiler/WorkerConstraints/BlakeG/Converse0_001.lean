module
public import Proven.Compiler.WorkerConstraints.BlakeG.Source
public import Proven.Compiler.WorkerConstraints.BlakeG.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields004

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement37 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 18) (by change 18 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement38 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 19) (by change 19 < 42; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  apply (refinement39 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 20) (by change 20 < 42; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeG)) :
    ∀ values ∈ tuple0_001 physical, ∃ index, values = NativeWorkerSetup.rows .blakeG 0 index :=
  (all_cons (backwards37 physical logical agreement holds) (all_cons (backwards38 physical logical agreement holds) (all_cons (backwards39 physical logical agreement holds) (by intro value member; cases member))))

end Airbender.Compiler.WorkerConstraints.BlakeG
