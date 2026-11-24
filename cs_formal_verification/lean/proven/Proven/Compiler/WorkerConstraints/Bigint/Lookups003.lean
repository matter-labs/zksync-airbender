module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Members004
public import Proven.Compiler.WorkerConstraints.Bigint.Members005
public import Proven.Compiler.WorkerConstraints.Bigint.Fields008
public import Proven.Compiler.WorkerConstraints.Bigint.Fields009
public import Proven.Compiler.WorkerConstraints.Bigint.Fields010

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups003 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∀ query ∈ queries003, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement70 physical logical agreement).mpr (member70 physical arguments)) (all_cons ((refinement71 physical logical agreement).mpr (member71 physical arguments)) (all_cons ((refinement72 physical logical agreement).mpr (member72 physical arguments)) (all_cons ((refinement73 physical logical agreement).mpr (member73 physical arguments)) (all_cons ((refinement74 physical logical agreement).mpr (member74 physical arguments)) (all_cons ((refinement75 physical logical agreement).mpr (member75 physical arguments)) (all_cons ((refinement76 physical logical agreement).mpr (member76 physical arguments)) (all_cons ((refinement77 physical logical agreement).mpr (member77 physical arguments)) (all_cons ((refinement78 physical logical agreement).mpr (member78 physical arguments)) (all_cons ((refinement79 physical logical agreement).mpr (member79 physical arguments)) (all_cons ((refinement80 physical logical agreement).mpr (member80 physical arguments)) (all_cons ((refinement81 physical logical agreement).mpr (member81 physical arguments)) (all_cons ((refinement82 physical logical agreement).mpr (member82 physical arguments)) (all_cons ((refinement83 physical logical agreement).mpr (member83 physical arguments)) (all_cons ((refinement84 physical logical agreement).mpr (member84 physical arguments)) (all_cons ((refinement85 physical logical agreement).mpr (member85 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
