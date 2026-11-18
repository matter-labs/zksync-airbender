module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members016
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members017
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields032
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields033
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields034

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups011 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries011, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement263 physical logical agreement).mpr (member263 physical arguments)) (all_cons ((refinement264 physical logical agreement).mpr (member264 physical arguments)) (all_cons ((refinement265 physical logical agreement).mpr (member265 physical arguments)) (all_cons ((refinement266 physical logical agreement).mpr (member266 physical arguments)) (all_cons ((refinement267 physical logical agreement).mpr (member267 physical arguments)) (all_cons ((refinement268 physical logical agreement).mpr (member268 physical arguments)) (all_cons ((refinement269 physical logical agreement).mpr (member269 physical arguments)) (all_cons ((refinement270 physical logical agreement).mpr (member270 physical arguments)) (all_cons ((refinement271 physical logical agreement).mpr (member271 physical arguments)) (all_cons ((refinement272 physical logical agreement).mpr (member272 physical arguments)) (all_cons ((refinement273 physical logical agreement).mpr (member273 physical arguments)) (all_cons ((refinement274 physical logical agreement).mpr (member274 physical arguments)) (all_cons ((refinement275 physical logical agreement).mpr (member275 physical arguments)) (all_cons ((refinement276 physical logical agreement).mpr (member276 physical arguments)) (all_cons ((refinement277 physical logical agreement).mpr (member277 physical arguments)) (all_cons ((refinement278 physical logical agreement).mpr (member278 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
