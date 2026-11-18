module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members005
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members006
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields010
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields011
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields012

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries000, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement87 physical logical agreement).mpr (member87 physical arguments)) (all_cons ((refinement88 physical logical agreement).mpr (member88 physical arguments)) (all_cons ((refinement89 physical logical agreement).mpr (member89 physical arguments)) (all_cons ((refinement90 physical logical agreement).mpr (member90 physical arguments)) (all_cons ((refinement91 physical logical agreement).mpr (member91 physical arguments)) (all_cons ((refinement92 physical logical agreement).mpr (member92 physical arguments)) (all_cons ((refinement93 physical logical agreement).mpr (member93 physical arguments)) (all_cons ((refinement94 physical logical agreement).mpr (member94 physical arguments)) (all_cons ((refinement95 physical logical agreement).mpr (member95 physical arguments)) (all_cons ((refinement96 physical logical agreement).mpr (member96 physical arguments)) (all_cons ((refinement97 physical logical agreement).mpr (member97 physical arguments)) (all_cons ((refinement98 physical logical agreement).mpr (member98 physical arguments)) (all_cons ((refinement99 physical logical agreement).mpr (member99 physical arguments)) (all_cons ((refinement100 physical logical agreement).mpr (member100 physical arguments)) (all_cons ((refinement101 physical logical agreement).mpr (member101 physical arguments)) (all_cons ((refinement102 physical logical agreement).mpr (member102 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
