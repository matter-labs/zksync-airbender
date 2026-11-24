module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Source
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Members000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Members001
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Fields000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Fields002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .chi5) (selectorsFor .chi5) physical (NativeWorkerSetup.rows .chi5)) :
    ∀ query ∈ queries001, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement16 physical logical agreement).mpr (member16 physical arguments)) (all_cons ((refinement17 physical logical agreement).mpr (member17 physical arguments)) (all_cons ((refinement0 physical logical agreement).mpr (member0 physical arguments)) (all_cons ((refinement18 physical logical agreement).mpr (member18 physical arguments)) (by intro value member; cases member)))))

end Airbender.Compiler.WorkerConstraints.KeccakChi5
