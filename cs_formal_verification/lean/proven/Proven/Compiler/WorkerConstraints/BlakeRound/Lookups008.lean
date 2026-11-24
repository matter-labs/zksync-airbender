module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members013
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members014
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields026
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields027
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields028

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups008 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries008, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement215 physical logical agreement).mpr (member215 physical arguments)) (all_cons ((refinement216 physical logical agreement).mpr (member216 physical arguments)) (all_cons ((refinement217 physical logical agreement).mpr (member217 physical arguments)) (all_cons ((refinement218 physical logical agreement).mpr (member218 physical arguments)) (all_cons ((refinement219 physical logical agreement).mpr (member219 physical arguments)) (all_cons ((refinement220 physical logical agreement).mpr (member220 physical arguments)) (all_cons ((refinement221 physical logical agreement).mpr (member221 physical arguments)) (all_cons ((refinement222 physical logical agreement).mpr (member222 physical arguments)) (all_cons ((refinement223 physical logical agreement).mpr (member223 physical arguments)) (all_cons ((refinement224 physical logical agreement).mpr (member224 physical arguments)) (all_cons ((refinement225 physical logical agreement).mpr (member225 physical arguments)) (all_cons ((refinement226 physical logical agreement).mpr (member226 physical arguments)) (all_cons ((refinement227 physical logical agreement).mpr (member227 physical arguments)) (all_cons ((refinement228 physical logical agreement).mpr (member228 physical arguments)) (all_cons ((refinement229 physical logical agreement).mpr (member229 physical arguments)) (all_cons ((refinement230 physical logical agreement).mpr (member230 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
