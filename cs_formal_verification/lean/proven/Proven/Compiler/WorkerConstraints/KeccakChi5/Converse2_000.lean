module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Source
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Fields000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Fields002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards0 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .chi5)) :
    ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .chi5 2 index := by
  apply (refinement0 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 18) (by change 18 < 20; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards18 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .chi5)) :
    ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .chi5 2 index := by
  apply (refinement18 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 0) (by change 0 < 20; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse2_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .chi5)) :
    ∀ values ∈ tuple2_000 physical, ∃ index, values = NativeWorkerSetup.rows .chi5 2 index :=
  (all_cons (backwards0 physical logical agreement holds) (all_cons (backwards18 physical logical agreement holds) (by intro value member; cases member)))

end Airbender.Compiler.WorkerConstraints.KeccakChi5
