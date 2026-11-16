module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members002
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members003
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields005
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields006
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields007

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups015 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries015, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement46 physical logical agreement).mpr (member46 physical arguments)) (all_cons ((refinement47 physical logical agreement).mpr (member47 physical arguments)) (all_cons ((refinement48 physical logical agreement).mpr (member48 physical arguments)) (all_cons ((refinement49 physical logical agreement).mpr (member49 physical arguments)) (all_cons ((refinement50 physical logical agreement).mpr (member50 physical arguments)) (all_cons ((refinement51 physical logical agreement).mpr (member51 physical arguments)) (all_cons ((refinement52 physical logical agreement).mpr (member52 physical arguments)) (all_cons ((refinement53 physical logical agreement).mpr (member53 physical arguments)) (all_cons ((refinement54 physical logical agreement).mpr (member54 physical arguments)) (all_cons ((refinement55 physical logical agreement).mpr (member55 physical arguments)) (all_cons ((refinement56 physical logical agreement).mpr (member56 physical arguments)) (all_cons ((refinement57 physical logical agreement).mpr (member57 physical arguments)) (all_cons ((refinement58 physical logical agreement).mpr (member58 physical arguments)) (all_cons ((refinement59 physical logical agreement).mpr (member59 physical arguments)) (all_cons ((refinement60 physical logical agreement).mpr (member60 physical arguments)) (all_cons ((refinement61 physical logical agreement).mpr (member61 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
