module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields023
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields024
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields025

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards185 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand185.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement185 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 98) (by change 98 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards186 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand186.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement186 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 99) (by change 99 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards187 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand187.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement187 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 100) (by change 100 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards188 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand188.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement188 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 101) (by change 101 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards189 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand189.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement189 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 102) (by change 102 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards190 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand190.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement190 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 103) (by change 103 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards191 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand191.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement191 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 104) (by change 104 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards192 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand192.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement192 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 105) (by change 105 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards193 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand193.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement193 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 106) (by change 106 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards194 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand194.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement194 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 107) (by change 107 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards195 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand195.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement195 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 108) (by change 108 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards196 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand196.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement196 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 109) (by change 109 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards197 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand197.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement197 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 110) (by change 110 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards198 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand198.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement198 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 111) (by change 111 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards199 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand199.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement199 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 112) (by change 112 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards200 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand200.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement200 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 113) (by change 113 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_006 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_006 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards185 physical logical agreement holds) (all_cons (backwards186 physical logical agreement holds) (all_cons (backwards187 physical logical agreement holds) (all_cons (backwards188 physical logical agreement holds) (all_cons (backwards189 physical logical agreement holds) (all_cons (backwards190 physical logical agreement holds) (all_cons (backwards191 physical logical agreement holds) (all_cons (backwards192 physical logical agreement holds) (all_cons (backwards193 physical logical agreement holds) (all_cons (backwards194 physical logical agreement holds) (all_cons (backwards195 physical logical agreement holds) (all_cons (backwards196 physical logical agreement holds) (all_cons (backwards197 physical logical agreement holds) (all_cons (backwards198 physical logical agreement holds) (all_cons (backwards199 physical logical agreement holds) (all_cons (backwards200 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
