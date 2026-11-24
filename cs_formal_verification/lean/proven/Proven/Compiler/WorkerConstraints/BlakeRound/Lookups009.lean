module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members014
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members015
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields028
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields029
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields030

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups009 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries009, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement231 physical logical agreement).mpr (member231 physical arguments)) (all_cons ((refinement232 physical logical agreement).mpr (member232 physical arguments)) (all_cons ((refinement233 physical logical agreement).mpr (member233 physical arguments)) (all_cons ((refinement234 physical logical agreement).mpr (member234 physical arguments)) (all_cons ((refinement235 physical logical agreement).mpr (member235 physical arguments)) (all_cons ((refinement236 physical logical agreement).mpr (member236 physical arguments)) (all_cons ((refinement237 physical logical agreement).mpr (member237 physical arguments)) (all_cons ((refinement238 physical logical agreement).mpr (member238 physical arguments)) (all_cons ((refinement239 physical logical agreement).mpr (member239 physical arguments)) (all_cons ((refinement240 physical logical agreement).mpr (member240 physical arguments)) (all_cons ((refinement241 physical logical agreement).mpr (member241 physical arguments)) (all_cons ((refinement242 physical logical agreement).mpr (member242 physical arguments)) (all_cons ((refinement243 physical logical agreement).mpr (member243 physical arguments)) (all_cons ((refinement244 physical logical agreement).mpr (member244 physical arguments)) (all_cons ((refinement245 physical logical agreement).mpr (member245 physical arguments)) (all_cons ((refinement246 physical logical agreement).mpr (member246 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
