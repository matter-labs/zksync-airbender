module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields002
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement16 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 210) (by change 210 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement17 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 211) (by change 211 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement18 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 212) (by change 212 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement19 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 213) (by change 213 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement20 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 214) (by change 214 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement21 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 215) (by change 215 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement22 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 216) (by change 216 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement23 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 217) (by change 217 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement24 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 218) (by change 218 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement25 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 219) (by change 219 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement26 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 220) (by change 220 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement27 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 221) (by change 221 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement28 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 222) (by change 222 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement29 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 223) (by change 223 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement30 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 224) (by change 224 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement31 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 225) (by change 225 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple2_001 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 2 index :=
  (all_cons (backwards16 physical logical agreement holds) (all_cons (backwards17 physical logical agreement holds) (all_cons (backwards18 physical logical agreement holds) (all_cons (backwards19 physical logical agreement holds) (all_cons (backwards20 physical logical agreement holds) (all_cons (backwards21 physical logical agreement holds) (all_cons (backwards22 physical logical agreement holds) (all_cons (backwards23 physical logical agreement holds) (all_cons (backwards24 physical logical agreement holds) (all_cons (backwards25 physical logical agreement holds) (all_cons (backwards26 physical logical agreement holds) (all_cons (backwards27 physical logical agreement holds) (all_cons (backwards28 physical logical agreement holds) (all_cons (backwards29 physical logical agreement holds) (all_cons (backwards30 physical logical agreement holds) (all_cons (backwards31 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
