module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields013
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields014
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields015

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards105 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand105.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement105 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 18) (by change 18 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards106 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand106.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement106 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 19) (by change 19 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards107 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand107.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement107 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 20) (by change 20 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards108 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand108.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement108 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 21) (by change 21 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards109 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand109.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement109 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 22) (by change 22 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards110 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand110.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement110 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 23) (by change 23 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards111 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand111.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement111 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 24) (by change 24 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards112 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand112.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement112 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 25) (by change 25 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards113 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand113.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement113 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 26) (by change 26 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards114 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand114.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement114 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 27) (by change 27 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards115 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand115.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement115 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 28) (by change 28 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards116 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand116.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement116 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 29) (by change 29 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards117 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand117.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement117 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 30) (by change 30 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards118 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand118.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement118 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 31) (by change 31 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards119 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand119.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement119 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 32) (by change 32 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards120 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand120.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement120 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 33) (by change 33 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_001 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards105 physical logical agreement holds) (all_cons (backwards106 physical logical agreement holds) (all_cons (backwards107 physical logical agreement holds) (all_cons (backwards108 physical logical agreement holds) (all_cons (backwards109 physical logical agreement holds) (all_cons (backwards110 physical logical agreement holds) (all_cons (backwards111 physical logical agreement holds) (all_cons (backwards112 physical logical agreement holds) (all_cons (backwards113 physical logical agreement holds) (all_cons (backwards114 physical logical agreement holds) (all_cons (backwards115 physical logical agreement holds) (all_cons (backwards116 physical logical agreement holds) (all_cons (backwards117 physical logical agreement holds) (all_cons (backwards118 physical logical agreement holds) (all_cons (backwards119 physical logical agreement holds) (all_cons (backwards120 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
