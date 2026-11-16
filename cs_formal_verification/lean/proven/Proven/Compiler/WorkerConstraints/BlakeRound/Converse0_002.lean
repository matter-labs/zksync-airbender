module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields015
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields016
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields017

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards121 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand121.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement121 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 34) (by change 34 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards122 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand122.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement122 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 35) (by change 35 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards123 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand123.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement123 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 36) (by change 36 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards124 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand124.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement124 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 37) (by change 37 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards125 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand125.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement125 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 38) (by change 38 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards126 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand126.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement126 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 39) (by change 39 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards127 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand127.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement127 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 40) (by change 40 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards128 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand128.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement128 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 41) (by change 41 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards129 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand129.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement129 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 42) (by change 42 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards130 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand130.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement130 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 43) (by change 43 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards131 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand131.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement131 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 44) (by change 44 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards132 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand132.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement132 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 45) (by change 45 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards133 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand133.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement133 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 46) (by change 46 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards134 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand134.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement134 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 47) (by change 47 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards135 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand135.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement135 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 48) (by change 48 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards136 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand136.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement136 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 49) (by change 49 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_002 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_002 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards121 physical logical agreement holds) (all_cons (backwards122 physical logical agreement holds) (all_cons (backwards123 physical logical agreement holds) (all_cons (backwards124 physical logical agreement holds) (all_cons (backwards125 physical logical agreement holds) (all_cons (backwards126 physical logical agreement holds) (all_cons (backwards127 physical logical agreement holds) (all_cons (backwards128 physical logical agreement holds) (all_cons (backwards129 physical logical agreement holds) (all_cons (backwards130 physical logical agreement holds) (all_cons (backwards131 physical logical agreement holds) (all_cons (backwards132 physical logical agreement holds) (all_cons (backwards133 physical logical agreement holds) (all_cons (backwards134 physical logical agreement holds) (all_cons (backwards135 physical logical agreement holds) (all_cons (backwards136 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
