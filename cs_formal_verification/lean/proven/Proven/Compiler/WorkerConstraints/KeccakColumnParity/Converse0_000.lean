module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Source
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields003
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields004
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields005

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement29 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 1) (by change 1 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement30 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 2) (by change 2 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement31 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 3) (by change 3 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement32 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 4) (by change 4 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement33 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 5) (by change 5 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement34 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 6) (by change 6 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement35 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 7) (by change 7 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement36 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 8) (by change 8 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement37 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 9) (by change 9 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement38 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 10) (by change 10 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement39 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 11) (by change 11 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand40.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement40 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 12) (by change 12 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand41.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement41 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 13) (by change 13 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand42.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement42 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 14) (by change 14 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand43.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement43 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 15) (by change 15 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∃ index, operand44.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  apply (refinement44 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 16) (by change 16 < 53; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .columnParity)) :
    ∀ values ∈ tuple0_000 physical, ∃ index, values = NativeWorkerSetup.rows .columnParity 0 index :=
  (all_cons (backwards29 physical logical agreement holds) (all_cons (backwards30 physical logical agreement holds) (all_cons (backwards31 physical logical agreement holds) (all_cons (backwards32 physical logical agreement holds) (all_cons (backwards33 physical logical agreement holds) (all_cons (backwards34 physical logical agreement holds) (all_cons (backwards35 physical logical agreement holds) (all_cons (backwards36 physical logical agreement holds) (all_cons (backwards37 physical logical agreement holds) (all_cons (backwards38 physical logical agreement holds) (all_cons (backwards39 physical logical agreement holds) (all_cons (backwards40 physical logical agreement holds) (all_cons (backwards41 physical logical agreement holds) (all_cons (backwards42 physical logical agreement holds) (all_cons (backwards43 physical logical agreement holds) (all_cons (backwards44 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
