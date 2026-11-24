module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members004
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members005
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields009
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields010
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields011

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups017 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries017, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement78 physical logical agreement).mpr (member78 physical arguments)) (all_cons ((refinement79 physical logical agreement).mpr (member79 physical arguments)) (all_cons ((refinement80 physical logical agreement).mpr (member80 physical arguments)) (all_cons ((refinement81 physical logical agreement).mpr (member81 physical arguments)) (all_cons ((refinement82 physical logical agreement).mpr (member82 physical arguments)) (all_cons ((refinement83 physical logical agreement).mpr (member83 physical arguments)) (all_cons ((refinement84 physical logical agreement).mpr (member84 physical arguments)) (all_cons ((refinement85 physical logical agreement).mpr (member85 physical arguments)) (all_cons ((refinement86 physical logical agreement).mpr (member86 physical arguments)) (all_cons ((refinement87 physical logical agreement).mpr (member87 physical arguments)) (all_cons ((refinement88 physical logical agreement).mpr (member88 physical arguments)) (by intro value member; cases member))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
