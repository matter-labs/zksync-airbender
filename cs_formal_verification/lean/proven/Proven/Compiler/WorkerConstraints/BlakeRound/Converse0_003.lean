module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields017
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields018
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields019

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards137 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand137.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement137 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 50) (by change 50 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards138 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand138.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement138 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 51) (by change 51 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards139 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand139.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement139 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 52) (by change 52 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards140 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand140.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement140 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 53) (by change 53 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards141 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand141.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement141 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 54) (by change 54 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards142 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand142.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement142 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 55) (by change 55 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards143 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand143.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement143 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 56) (by change 56 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards144 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand144.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement144 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 57) (by change 57 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards145 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand145.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement145 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 58) (by change 58 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards146 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand146.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement146 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 59) (by change 59 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards147 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand147.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement147 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 60) (by change 60 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards148 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand148.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement148 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 61) (by change 61 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards149 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand149.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement149 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 62) (by change 62 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards150 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand150.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement150 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 63) (by change 63 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards151 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand151.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement151 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 64) (by change 64 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards152 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand152.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement152 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 65) (by change 65 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_003 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_003 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards137 physical logical agreement holds) (all_cons (backwards138 physical logical agreement holds) (all_cons (backwards139 physical logical agreement holds) (all_cons (backwards140 physical logical agreement holds) (all_cons (backwards141 physical logical agreement holds) (all_cons (backwards142 physical logical agreement holds) (all_cons (backwards143 physical logical agreement holds) (all_cons (backwards144 physical logical agreement holds) (all_cons (backwards145 physical logical agreement holds) (all_cons (backwards146 physical logical agreement holds) (all_cons (backwards147 physical logical agreement holds) (all_cons (backwards148 physical logical agreement holds) (all_cons (backwards149 physical logical agreement holds) (all_cons (backwards150 physical logical agreement holds) (all_cons (backwards151 physical logical agreement holds) (all_cons (backwards152 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
