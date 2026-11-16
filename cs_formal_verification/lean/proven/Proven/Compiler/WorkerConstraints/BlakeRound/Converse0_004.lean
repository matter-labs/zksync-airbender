module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields019
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields020
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields021

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards153 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand153.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement153 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 66) (by change 66 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards154 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand154.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement154 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 67) (by change 67 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards155 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand155.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement155 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 68) (by change 68 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards156 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand156.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement156 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 69) (by change 69 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards157 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand157.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement157 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 70) (by change 70 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards158 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand158.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement158 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 71) (by change 71 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards159 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand159.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement159 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 72) (by change 72 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards160 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand160.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement160 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 73) (by change 73 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards161 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand161.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement161 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 74) (by change 74 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards162 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand162.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement162 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 75) (by change 75 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards163 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand163.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement163 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 76) (by change 76 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards164 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand164.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement164 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 77) (by change 77 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards165 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand165.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement165 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 78) (by change 78 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards166 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand166.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement166 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 79) (by change 79 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards167 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand167.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement167 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 80) (by change 80 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards168 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand168.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement168 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 81) (by change 81 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_004 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_004 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards153 physical logical agreement holds) (all_cons (backwards154 physical logical agreement holds) (all_cons (backwards155 physical logical agreement holds) (all_cons (backwards156 physical logical agreement holds) (all_cons (backwards157 physical logical agreement holds) (all_cons (backwards158 physical logical agreement holds) (all_cons (backwards159 physical logical agreement holds) (all_cons (backwards160 physical logical agreement holds) (all_cons (backwards161 physical logical agreement holds) (all_cons (backwards162 physical logical agreement holds) (all_cons (backwards163 physical logical agreement holds) (all_cons (backwards164 physical logical agreement holds) (all_cons (backwards165 physical logical agreement holds) (all_cons (backwards166 physical logical agreement holds) (all_cons (backwards167 physical logical agreement holds) (all_cons (backwards168 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
