module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Source
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields005
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand45.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement45 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 17) (by change 17 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand46.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement46 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 18) (by change 18 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand47.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement47 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 19) (by change 19 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement48 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 20) (by change 20 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement49 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 21) (by change 21 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement51 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 22) (by change 22 < 53; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∀ values ∈ tuple0_001 physical, ∃ index, values = NativeWorkerSetup.rows .columnParity 0 index :=
  (all_cons (backwards45 physical logical agreement holds) (all_cons (backwards46 physical logical agreement holds) (all_cons (backwards47 physical logical agreement holds) (all_cons (backwards48 physical logical agreement holds) (all_cons (backwards49 physical logical agreement holds) (all_cons (backwards51 physical logical agreement holds) (by intro value member; cases member)))))))

end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
