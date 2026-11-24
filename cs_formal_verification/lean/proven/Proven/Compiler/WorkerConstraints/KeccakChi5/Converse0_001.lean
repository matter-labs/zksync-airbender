module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Source
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Fields002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards17 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .chi5)) :
    ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  apply (refinement17 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 17) (by change 17 < 20; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .chi5)) :
    ∀ values ∈ tuple0_001 physical, ∃ index, values = NativeWorkerSetup.rows .chi5 0 index :=
  (all_cons (backwards17 physical logical agreement holds) (by intro value member; cases member))

end Airbender.Compiler.WorkerConstraints.KeccakChi5
