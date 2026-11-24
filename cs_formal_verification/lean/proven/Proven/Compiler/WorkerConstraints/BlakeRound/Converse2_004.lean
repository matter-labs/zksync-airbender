module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields008
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields009

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards64 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand64.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement64 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 258) (by change 258 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards65 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand65.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement65 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 259) (by change 259 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards66 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand66.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement66 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 260) (by change 260 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards67 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand67.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement67 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 261) (by change 261 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards68 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand68.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement68 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 262) (by change 262 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards69 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand69.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement69 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 263) (by change 263 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards70 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand70.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement70 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 264) (by change 264 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards71 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand71.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement71 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 265) (by change 265 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards72 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand72.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement72 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 266) (by change 266 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards73 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand73.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement73 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 267) (by change 267 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards74 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand74.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement74 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 268) (by change 268 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards75 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand75.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement75 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 269) (by change 269 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards76 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand76.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement76 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 270) (by change 270 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards77 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand77.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement77 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 271) (by change 271 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards78 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand78.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement78 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 272) (by change 272 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards79 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand79.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement79 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 273) (by change 273 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_004 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple2_004 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 2 index :=
  (all_cons (backwards64 physical logical agreement holds) (all_cons (backwards65 physical logical agreement holds) (all_cons (backwards66 physical logical agreement holds) (all_cons (backwards67 physical logical agreement holds) (all_cons (backwards68 physical logical agreement holds) (all_cons (backwards69 physical logical agreement holds) (all_cons (backwards70 physical logical agreement holds) (all_cons (backwards71 physical logical agreement holds) (all_cons (backwards72 physical logical agreement holds) (all_cons (backwards73 physical logical agreement holds) (all_cons (backwards74 physical logical agreement holds) (all_cons (backwards75 physical logical agreement holds) (all_cons (backwards76 physical logical agreement holds) (all_cons (backwards77 physical logical agreement holds) (all_cons (backwards78 physical logical agreement holds) (all_cons (backwards79 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
