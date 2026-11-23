module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields029
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields030
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields031

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards233 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand233.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement233 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 146) (by change 146 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards234 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand234.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement234 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 147) (by change 147 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards235 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand235.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement235 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 148) (by change 148 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards236 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand236.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement236 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 149) (by change 149 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards237 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand237.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement237 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 150) (by change 150 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards238 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand238.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement238 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 151) (by change 151 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards239 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand239.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement239 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 152) (by change 152 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards240 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand240.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement240 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 153) (by change 153 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards241 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand241.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement241 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 154) (by change 154 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards242 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand242.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement242 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 155) (by change 155 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards243 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand243.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement243 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 156) (by change 156 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards244 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand244.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement244 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 157) (by change 157 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards245 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand245.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement245 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 158) (by change 158 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards246 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand246.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement246 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 159) (by change 159 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards247 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand247.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement247 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 160) (by change 160 < 283; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards248 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∃ index, operand248.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  apply (refinement248 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 161) (by change 161 < 283; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_009 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .blakeRound)) :
    ∀ values ∈ tuple0_009 physical, ∃ index, values = NativeWorkerSetup.rows .blakeRound 0 index :=
  (all_cons (backwards233 physical logical agreement holds) (all_cons (backwards234 physical logical agreement holds) (all_cons (backwards235 physical logical agreement holds) (all_cons (backwards236 physical logical agreement holds) (all_cons (backwards237 physical logical agreement holds) (all_cons (backwards238 physical logical agreement holds) (all_cons (backwards239 physical logical agreement holds) (all_cons (backwards240 physical logical agreement holds) (all_cons (backwards241 physical logical agreement holds) (all_cons (backwards242 physical logical agreement holds) (all_cons (backwards243 physical logical agreement holds) (all_cons (backwards244 physical logical agreement holds) (all_cons (backwards245 physical logical agreement holds) (all_cons (backwards246 physical logical agreement holds) (all_cons (backwards247 physical logical agreement holds) (all_cons (backwards248 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
