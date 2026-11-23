module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields011
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields012
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields013

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards89 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand89.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement89 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 2) (by change 2 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards90 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand90.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement90 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 3) (by change 3 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards91 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand91.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement91 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 4) (by change 4 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards92 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand92.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement92 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 5) (by change 5 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards93 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand93.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement93 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 6) (by change 6 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards94 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand94.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement94 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 7) (by change 7 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards95 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand95.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement95 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 8) (by change 8 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards96 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand96.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement96 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 9) (by change 9 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards97 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand97.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement97 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 10) (by change 10 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards98 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand98.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement98 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 11) (by change 11 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards99 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand99.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement99 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 12) (by change 12 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards100 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand100.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement100 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 13) (by change 13 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards101 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand101.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement101 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 14) (by change 14 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards102 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand102.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement102 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 15) (by change 15 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards103 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand103.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement103 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 16) (by change 16 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards104 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand104.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement104 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 17) (by change 17 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_000 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards89 physical logical agreement holds) (all_cons (backwards90 physical logical agreement holds) (all_cons (backwards91 physical logical agreement holds) (all_cons (backwards92 physical logical agreement holds) (all_cons (backwards93 physical logical agreement holds) (all_cons (backwards94 physical logical agreement holds) (all_cons (backwards95 physical logical agreement holds) (all_cons (backwards96 physical logical agreement holds) (all_cons (backwards97 physical logical agreement holds) (all_cons (backwards98 physical logical agreement holds) (all_cons (backwards99 physical logical agreement holds) (all_cons (backwards100 physical logical agreement holds) (all_cons (backwards101 physical logical agreement holds) (all_cons (backwards102 physical logical agreement holds) (all_cons (backwards103 physical logical agreement holds) (all_cons (backwards104 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
