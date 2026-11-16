module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Source
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards49 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement49 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 49) (by change 49 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards51 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement51 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 50) (by change 50 < 53; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_003 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∀ values ∈ tuple0_003 physical, ∃ index, values = NativeWorkerSetup.rows .thetaRho 0 index :=
  (all_cons (backwards49 physical logical agreement holds) (all_cons (backwards51 physical logical agreement holds) (by intro value member; cases member)))

end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
