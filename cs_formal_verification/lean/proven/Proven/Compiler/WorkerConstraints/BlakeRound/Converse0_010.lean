module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields031
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields032
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields033

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards249 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand249.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement249 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 162) (by change 162 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards250 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand250.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement250 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 163) (by change 163 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards251 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand251.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement251 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 164) (by change 164 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards252 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand252.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement252 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 165) (by change 165 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards253 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand253.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement253 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 166) (by change 166 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards254 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand254.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement254 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 167) (by change 167 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards255 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand255.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement255 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 168) (by change 168 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards256 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand256.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement256 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 169) (by change 169 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards257 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand257.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement257 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 170) (by change 170 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards258 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand258.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement258 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 171) (by change 171 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards259 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand259.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement259 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 172) (by change 172 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards260 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand260.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement260 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 173) (by change 173 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards261 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand261.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement261 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 174) (by change 174 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards262 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand262.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement262 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 175) (by change 175 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards263 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand263.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement263 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 176) (by change 176 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards264 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand264.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement264 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 177) (by change 177 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_010 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_010 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards249 physical logical agreement holds) (all_cons (backwards250 physical logical agreement holds) (all_cons (backwards251 physical logical agreement holds) (all_cons (backwards252 physical logical agreement holds) (all_cons (backwards253 physical logical agreement holds) (all_cons (backwards254 physical logical agreement holds) (all_cons (backwards255 physical logical agreement holds) (all_cons (backwards256 physical logical agreement holds) (all_cons (backwards257 physical logical agreement holds) (all_cons (backwards258 physical logical agreement holds) (all_cons (backwards259 physical logical agreement holds) (all_cons (backwards260 physical logical agreement holds) (all_cons (backwards261 physical logical agreement holds) (all_cons (backwards262 physical logical agreement holds) (all_cons (backwards263 physical logical agreement holds) (all_cons (backwards264 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
