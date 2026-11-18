module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields021
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields022
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields023

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards169 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand169.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement169 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 82) (by change 82 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards170 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand170.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement170 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 83) (by change 83 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards171 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand171.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement171 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 84) (by change 84 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards172 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand172.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement172 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 85) (by change 85 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards173 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand173.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement173 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 86) (by change 86 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards174 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand174.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement174 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 87) (by change 87 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards175 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand175.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement175 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 88) (by change 88 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards176 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand176.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement176 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 89) (by change 89 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards177 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand177.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement177 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 90) (by change 90 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards178 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand178.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement178 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 91) (by change 91 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards179 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand179.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement179 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 92) (by change 92 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards180 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand180.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement180 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 93) (by change 93 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards181 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand181.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement181 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 94) (by change 94 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards182 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand182.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement182 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 95) (by change 95 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards183 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand183.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement183 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 96) (by change 96 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards184 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand184.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement184 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 97) (by change 97 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_005 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_005 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards169 physical logical agreement holds) (all_cons (backwards170 physical logical agreement holds) (all_cons (backwards171 physical logical agreement holds) (all_cons (backwards172 physical logical agreement holds) (all_cons (backwards173 physical logical agreement holds) (all_cons (backwards174 physical logical agreement holds) (all_cons (backwards175 physical logical agreement holds) (all_cons (backwards176 physical logical agreement holds) (all_cons (backwards177 physical logical agreement holds) (all_cons (backwards178 physical logical agreement holds) (all_cons (backwards179 physical logical agreement holds) (all_cons (backwards180 physical logical agreement holds) (all_cons (backwards181 physical logical agreement holds) (all_cons (backwards182 physical logical agreement holds) (all_cons (backwards183 physical logical agreement holds) (all_cons (backwards184 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
