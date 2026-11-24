module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields006
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields007

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement48 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 242) (by change 242 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement49 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 243) (by change 243 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement50 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 244) (by change 244 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement51 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 245) (by change 245 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards52 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand52.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement52 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 246) (by change 246 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards53 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand53.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement53 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 247) (by change 247 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards54 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand54.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement54 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 248) (by change 248 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards55 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand55.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement55 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 249) (by change 249 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards56 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand56.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement56 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 250) (by change 250 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards57 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand57.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement57 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 251) (by change 251 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards58 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand58.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement58 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 252) (by change 252 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards59 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand59.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement59 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 253) (by change 253 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards60 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand60.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement60 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 254) (by change 254 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards61 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand61.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement61 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 255) (by change 255 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards62 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand62.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement62 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 256) (by change 256 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards63 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand63.input.fields physical = NativeWorkerSetup.rows .blakeRound 2 index := by
  apply (refinement63 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 257) (by change 257 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_003 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple2_003 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 2 index :=
  (all_cons (backwards48 physical logical agreement holds) (all_cons (backwards49 physical logical agreement holds) (all_cons (backwards50 physical logical agreement holds) (all_cons (backwards51 physical logical agreement holds) (all_cons (backwards52 physical logical agreement holds) (all_cons (backwards53 physical logical agreement holds) (all_cons (backwards54 physical logical agreement holds) (all_cons (backwards55 physical logical agreement holds) (all_cons (backwards56 physical logical agreement holds) (all_cons (backwards57 physical logical agreement holds) (all_cons (backwards58 physical logical agreement holds) (all_cons (backwards59 physical logical agreement holds) (all_cons (backwards60 physical logical agreement holds) (all_cons (backwards61 physical logical agreement holds) (all_cons (backwards62 physical logical agreement holds) (all_cons (backwards63 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
