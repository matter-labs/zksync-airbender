module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Source
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields002
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields003
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields004

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement17 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 17) (by change 17 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement18 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 18) (by change 18 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards19 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement19 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 19) (by change 19 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards20 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement20 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 20) (by change 20 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards21 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement21 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 21) (by change 21 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards22 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement22 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 22) (by change 22 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards23 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement23 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 23) (by change 23 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards24 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement24 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 24) (by change 24 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards25 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement25 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 25) (by change 25 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards26 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement26 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 26) (by change 26 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards27 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement27 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 27) (by change 27 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards28 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement28 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 28) (by change 28 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards29 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement29 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 29) (by change 29 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards30 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement30 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 30) (by change 30 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards31 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement31 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 31) (by change 31 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards32 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement32 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 32) (by change 32 < 53; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∀ values ∈ tuple0_001 physical, ∃ index, values = NativeWorkerSetup.rows .thetaRho 0 index :=
  (all_cons (backwards17 physical logical agreement holds) (all_cons (backwards18 physical logical agreement holds) (all_cons (backwards19 physical logical agreement holds) (all_cons (backwards20 physical logical agreement holds) (all_cons (backwards21 physical logical agreement holds) (all_cons (backwards22 physical logical agreement holds) (all_cons (backwards23 physical logical agreement holds) (all_cons (backwards24 physical logical agreement holds) (all_cons (backwards25 physical logical agreement holds) (all_cons (backwards26 physical logical agreement holds) (all_cons (backwards27 physical logical agreement holds) (all_cons (backwards28 physical logical agreement holds) (all_cons (backwards29 physical logical agreement holds) (all_cons (backwards30 physical logical agreement holds) (all_cons (backwards31 physical logical agreement holds) (all_cons (backwards32 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
