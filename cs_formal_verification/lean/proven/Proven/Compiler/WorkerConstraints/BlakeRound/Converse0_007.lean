module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields025
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields026
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields027

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards201 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand201.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement201 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 114) (by change 114 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards202 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand202.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement202 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 115) (by change 115 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards203 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand203.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement203 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 116) (by change 116 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards204 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand204.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement204 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 117) (by change 117 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards205 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand205.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement205 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 118) (by change 118 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards206 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand206.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement206 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 119) (by change 119 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards207 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand207.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement207 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 120) (by change 120 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards208 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand208.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement208 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 121) (by change 121 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards209 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand209.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement209 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 122) (by change 122 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards210 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand210.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement210 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 123) (by change 123 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards211 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand211.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement211 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 124) (by change 124 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards212 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand212.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement212 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 125) (by change 125 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards213 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand213.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement213 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 126) (by change 126 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards214 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand214.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement214 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 127) (by change 127 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards215 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand215.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement215 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 128) (by change 128 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards216 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand216.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement216 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 129) (by change 129 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_007 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_007 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards201 physical logical agreement holds) (all_cons (backwards202 physical logical agreement holds) (all_cons (backwards203 physical logical agreement holds) (all_cons (backwards204 physical logical agreement holds) (all_cons (backwards205 physical logical agreement holds) (all_cons (backwards206 physical logical agreement holds) (all_cons (backwards207 physical logical agreement holds) (all_cons (backwards208 physical logical agreement holds) (all_cons (backwards209 physical logical agreement holds) (all_cons (backwards210 physical logical agreement holds) (all_cons (backwards211 physical logical agreement holds) (all_cons (backwards212 physical logical agreement holds) (all_cons (backwards213 physical logical agreement holds) (all_cons (backwards214 physical logical agreement holds) (all_cons (backwards215 physical logical agreement holds) (all_cons (backwards216 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
