module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members011
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members012
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields022
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields023
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields024

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups006 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries006, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement183 physical logical agreement).mpr (member183 physical arguments)) (all_cons ((refinement184 physical logical agreement).mpr (member184 physical arguments)) (all_cons ((refinement185 physical logical agreement).mpr (member185 physical arguments)) (all_cons ((refinement186 physical logical agreement).mpr (member186 physical arguments)) (all_cons ((refinement187 physical logical agreement).mpr (member187 physical arguments)) (all_cons ((refinement188 physical logical agreement).mpr (member188 physical arguments)) (all_cons ((refinement189 physical logical agreement).mpr (member189 physical arguments)) (all_cons ((refinement190 physical logical agreement).mpr (member190 physical arguments)) (all_cons ((refinement191 physical logical agreement).mpr (member191 physical arguments)) (all_cons ((refinement192 physical logical agreement).mpr (member192 physical arguments)) (all_cons ((refinement193 physical logical agreement).mpr (member193 physical arguments)) (all_cons ((refinement194 physical logical agreement).mpr (member194 physical arguments)) (all_cons ((refinement195 physical logical agreement).mpr (member195 physical arguments)) (all_cons ((refinement196 physical logical agreement).mpr (member196 physical arguments)) (all_cons ((refinement197 physical logical agreement).mpr (member197 physical arguments)) (all_cons ((refinement198 physical logical agreement).mpr (member198 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
