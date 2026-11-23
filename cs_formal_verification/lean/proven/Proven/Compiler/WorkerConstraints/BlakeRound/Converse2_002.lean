module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields004
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields005

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement32 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 226) (by change 226 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement33 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 227) (by change 227 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement34 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 228) (by change 228 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement35 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 229) (by change 229 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement36 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 230) (by change 230 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement37 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 231) (by change 231 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement38 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 232) (by change 232 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement39 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 233) (by change 233 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand40.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement40 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 234) (by change 234 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand41.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement41 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 235) (by change 235 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand42.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement42 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 236) (by change 236 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand43.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement43 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 237) (by change 237 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand44.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement44 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 238) (by change 238 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand45.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement45 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 239) (by change 239 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand46.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement46 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 240) (by change 240 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand47.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement47 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 241) (by change 241 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_002 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple2_002 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 2 index :=
  (all_cons (backwards32 physical logical agreement holds) (all_cons (backwards33 physical logical agreement holds) (all_cons (backwards34 physical logical agreement holds) (all_cons (backwards35 physical logical agreement holds) (all_cons (backwards36 physical logical agreement holds) (all_cons (backwards37 physical logical agreement holds) (all_cons (backwards38 physical logical agreement holds) (all_cons (backwards39 physical logical agreement holds) (all_cons (backwards40 physical logical agreement holds) (all_cons (backwards41 physical logical agreement holds) (all_cons (backwards42 physical logical agreement holds) (all_cons (backwards43 physical logical agreement holds) (all_cons (backwards44 physical logical agreement holds) (all_cons (backwards45 physical logical agreement holds) (all_cons (backwards46 physical logical agreement holds) (all_cons (backwards47 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
