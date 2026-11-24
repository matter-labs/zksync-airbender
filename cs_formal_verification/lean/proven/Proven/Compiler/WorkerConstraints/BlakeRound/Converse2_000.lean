module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields000
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields001

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement0 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 194) (by change 194 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement1 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 195) (by change 195 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement2 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 196) (by change 196 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement3 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 197) (by change 197 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement4 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 198) (by change 198 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement5 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 199) (by change 199 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement6 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 200) (by change 200 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement7 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 201) (by change 201 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement8 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 202) (by change 202 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement9 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 203) (by change 203 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement10 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 204) (by change 204 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement11 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 205) (by change 205 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement12 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 206) (by change 206 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement13 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 207) (by change 207 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement14 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 208) (by change 208 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement15 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 209) (by change 209 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple2_000 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 2 index :=
  (all_cons (backwards0 physical logical agreement holds) (all_cons (backwards1 physical logical agreement holds) (all_cons (backwards2 physical logical agreement holds) (all_cons (backwards3 physical logical agreement holds) (all_cons (backwards4 physical logical agreement holds) (all_cons (backwards5 physical logical agreement holds) (all_cons (backwards6 physical logical agreement holds) (all_cons (backwards7 physical logical agreement holds) (all_cons (backwards8 physical logical agreement holds) (all_cons (backwards9 physical logical agreement holds) (all_cons (backwards10 physical logical agreement holds) (all_cons (backwards11 physical logical agreement holds) (all_cons (backwards12 physical logical agreement holds) (all_cons (backwards13 physical logical agreement holds) (all_cons (backwards14 physical logical agreement holds) (all_cons (backwards15 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
