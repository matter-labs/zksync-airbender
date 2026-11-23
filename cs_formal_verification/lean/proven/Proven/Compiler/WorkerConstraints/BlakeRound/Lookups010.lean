module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members015
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members016
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields030
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields031
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields032

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups010 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries010, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement247 physical logical agreement).mpr (member247 physical arguments)) (all_cons ((refinement248 physical logical agreement).mpr (member248 physical arguments)) (all_cons ((refinement249 physical logical agreement).mpr (member249 physical arguments)) (all_cons ((refinement250 physical logical agreement).mpr (member250 physical arguments)) (all_cons ((refinement251 physical logical agreement).mpr (member251 physical arguments)) (all_cons ((refinement252 physical logical agreement).mpr (member252 physical arguments)) (all_cons ((refinement253 physical logical agreement).mpr (member253 physical arguments)) (all_cons ((refinement254 physical logical agreement).mpr (member254 physical arguments)) (all_cons ((refinement255 physical logical agreement).mpr (member255 physical arguments)) (all_cons ((refinement256 physical logical agreement).mpr (member256 physical arguments)) (all_cons ((refinement257 physical logical agreement).mpr (member257 physical arguments)) (all_cons ((refinement258 physical logical agreement).mpr (member258 physical arguments)) (all_cons ((refinement259 physical logical agreement).mpr (member259 physical arguments)) (all_cons ((refinement260 physical logical agreement).mpr (member260 physical arguments)) (all_cons ((refinement261 physical logical agreement).mpr (member261 physical arguments)) (all_cons ((refinement262 physical logical agreement).mpr (member262 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
