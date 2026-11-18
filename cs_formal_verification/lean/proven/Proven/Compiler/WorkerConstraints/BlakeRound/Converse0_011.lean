module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields033
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields034
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields035

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards265 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand265.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement265 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 178) (by change 178 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards266 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand266.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement266 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 179) (by change 179 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards267 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand267.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement267 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 180) (by change 180 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards268 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand268.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement268 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 181) (by change 181 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards269 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand269.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement269 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 182) (by change 182 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards270 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand270.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement270 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 183) (by change 183 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards271 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand271.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement271 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 184) (by change 184 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards272 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand272.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement272 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 185) (by change 185 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards273 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand273.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement273 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 186) (by change 186 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards274 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand274.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement274 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 187) (by change 187 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards275 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand275.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement275 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 188) (by change 188 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards276 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand276.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement276 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 189) (by change 189 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards277 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand277.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement277 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 190) (by change 190 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards278 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand278.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement278 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 191) (by change 191 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards279 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand279.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement279 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 192) (by change 192 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards280 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand280.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement280 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 193) (by change 193 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_011 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_011 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards265 physical logical agreement holds) (all_cons (backwards266 physical logical agreement holds) (all_cons (backwards267 physical logical agreement holds) (all_cons (backwards268 physical logical agreement holds) (all_cons (backwards269 physical logical agreement holds) (all_cons (backwards270 physical logical agreement holds) (all_cons (backwards271 physical logical agreement holds) (all_cons (backwards272 physical logical agreement holds) (all_cons (backwards273 physical logical agreement holds) (all_cons (backwards274 physical logical agreement holds) (all_cons (backwards275 physical logical agreement holds) (all_cons (backwards276 physical logical agreement holds) (all_cons (backwards277 physical logical agreement holds) (all_cons (backwards278 physical logical agreement holds) (all_cons (backwards279 physical logical agreement holds) (all_cons (backwards280 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
