module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Members003
public import Proven.Compiler.WorkerConstraints.Bigint.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups008 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∀ query ∈ queries008, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement48 physical logical agreement).mpr (member48 physical arguments)) (all_cons ((refinement49 physical logical agreement).mpr (member49 physical arguments)) (all_cons ((refinement50 physical logical agreement).mpr (member50 physical arguments)) (all_cons ((refinement51 physical logical agreement).mpr (member51 physical arguments)) (all_cons ((refinement52 physical logical agreement).mpr (member52 physical arguments)) (all_cons ((refinement53 physical logical agreement).mpr (member53 physical arguments)) (all_cons ((refinement54 physical logical agreement).mpr (member54 physical arguments)) (all_cons ((refinement55 physical logical agreement).mpr (member55 physical arguments)) (by intro value member; cases member)))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
