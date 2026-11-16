module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Members003
public import Proven.Compiler.WorkerConstraints.Bigint.Members004
public import Proven.Compiler.WorkerConstraints.Bigint.Fields006
public import Proven.Compiler.WorkerConstraints.Bigint.Fields007
public import Proven.Compiler.WorkerConstraints.Bigint.Fields008

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups002 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∀ query ∈ queries002, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement54 physical logical agreement).mpr (member54 physical arguments)) (all_cons ((refinement55 physical logical agreement).mpr (member55 physical arguments)) (all_cons ((refinement56 physical logical agreement).mpr (member56 physical arguments)) (all_cons ((refinement57 physical logical agreement).mpr (member57 physical arguments)) (all_cons ((refinement58 physical logical agreement).mpr (member58 physical arguments)) (all_cons ((refinement59 physical logical agreement).mpr (member59 physical arguments)) (all_cons ((refinement60 physical logical agreement).mpr (member60 physical arguments)) (all_cons ((refinement61 physical logical agreement).mpr (member61 physical arguments)) (all_cons ((refinement62 physical logical agreement).mpr (member62 physical arguments)) (all_cons ((refinement63 physical logical agreement).mpr (member63 physical arguments)) (all_cons ((refinement64 physical logical agreement).mpr (member64 physical arguments)) (all_cons ((refinement65 physical logical agreement).mpr (member65 physical arguments)) (all_cons ((refinement66 physical logical agreement).mpr (member66 physical arguments)) (all_cons ((refinement67 physical logical agreement).mpr (member67 physical arguments)) (all_cons ((refinement68 physical logical agreement).mpr (member68 physical arguments)) (all_cons ((refinement69 physical logical agreement).mpr (member69 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
