module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Source
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields004
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields005
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards33 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement33 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 33) (by change 33 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards34 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement34 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 34) (by change 34 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards35 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement35 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 35) (by change 35 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards36 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement36 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 36) (by change 36 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards37 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement37 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 37) (by change 37 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards38 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement38 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 38) (by change 38 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards39 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement39 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 39) (by change 39 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards40 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand40.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement40 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 40) (by change 40 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards41 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand41.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement41 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 41) (by change 41 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards42 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand42.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement42 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 42) (by change 42 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards43 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand43.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement43 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 43) (by change 43 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards44 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand44.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement44 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 44) (by change 44 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards45 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand45.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement45 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 45) (by change 45 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards46 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand46.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement46 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 46) (by change 46 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards47 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand47.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement47 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 47) (by change 47 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards48 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement48 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 48) (by change 48 < 53; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_002 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∀ values ∈ tuple0_002 physical, ∃ index, values = NativeWorkerSetup.rows .thetaRho 0 index :=
  (all_cons (backwards33 physical logical agreement holds) (all_cons (backwards34 physical logical agreement holds) (all_cons (backwards35 physical logical agreement holds) (all_cons (backwards36 physical logical agreement holds) (all_cons (backwards37 physical logical agreement holds) (all_cons (backwards38 physical logical agreement holds) (all_cons (backwards39 physical logical agreement holds) (all_cons (backwards40 physical logical agreement holds) (all_cons (backwards41 physical logical agreement holds) (all_cons (backwards42 physical logical agreement holds) (all_cons (backwards43 physical logical agreement holds) (all_cons (backwards44 physical logical agreement holds) (all_cons (backwards45 physical logical agreement holds) (all_cons (backwards46 physical logical agreement holds) (all_cons (backwards47 physical logical agreement holds) (all_cons (backwards48 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
