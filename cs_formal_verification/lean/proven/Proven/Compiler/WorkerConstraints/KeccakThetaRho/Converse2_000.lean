module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Source
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields000
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .thetaRho 2 index := by
  apply (refinement0 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 51) (by change 51 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards50 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .thetaRho 2 index := by
  apply (refinement50 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 0) (by change 0 < 53; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∀ values ∈ tuple2_000 physical, ∃ index, values = NativeWorkerSetup.rows .thetaRho 2 index :=
  (all_cons (backwards0 physical logical agreement holds) (all_cons (backwards50 physical logical agreement holds) (by intro value member; cases member)))

end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
