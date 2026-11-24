module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields027
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields028
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields029

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards217 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand217.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement217 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 130) (by change 130 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards218 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand218.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement218 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 131) (by change 131 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards219 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand219.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement219 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 132) (by change 132 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards220 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand220.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement220 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 133) (by change 133 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards221 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand221.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement221 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 134) (by change 134 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards222 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand222.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement222 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 135) (by change 135 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards223 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand223.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement223 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 136) (by change 136 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards224 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand224.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement224 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 137) (by change 137 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards225 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand225.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement225 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 138) (by change 138 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards226 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand226.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement226 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 139) (by change 139 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards227 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand227.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement227 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 140) (by change 140 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards228 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand228.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement228 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 141) (by change 141 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards229 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand229.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement229 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 142) (by change 142 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards230 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand230.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement230 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 143) (by change 143 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards231 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand231.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement231 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 144) (by change 144 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards232 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand232.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement232 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 145) (by change 145 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_008 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_008 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards217 physical logical agreement holds) (all_cons (backwards218 physical logical agreement holds) (all_cons (backwards219 physical logical agreement holds) (all_cons (backwards220 physical logical agreement holds) (all_cons (backwards221 physical logical agreement holds) (all_cons (backwards222 physical logical agreement holds) (all_cons (backwards223 physical logical agreement holds) (all_cons (backwards224 physical logical agreement holds) (all_cons (backwards225 physical logical agreement holds) (all_cons (backwards226 physical logical agreement holds) (all_cons (backwards227 physical logical agreement holds) (all_cons (backwards228 physical logical agreement holds) (all_cons (backwards229 physical logical agreement holds) (all_cons (backwards230 physical logical agreement holds) (all_cons (backwards231 physical logical agreement holds) (all_cons (backwards232 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
