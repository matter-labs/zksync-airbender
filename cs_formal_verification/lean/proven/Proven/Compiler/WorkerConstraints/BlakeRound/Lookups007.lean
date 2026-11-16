module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members012
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members013
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields024
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields025
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields026

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups007 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries007, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement199 physical logical agreement).mpr (member199 physical arguments)) (all_cons ((refinement200 physical logical agreement).mpr (member200 physical arguments)) (all_cons ((refinement201 physical logical agreement).mpr (member201 physical arguments)) (all_cons ((refinement202 physical logical agreement).mpr (member202 physical arguments)) (all_cons ((refinement203 physical logical agreement).mpr (member203 physical arguments)) (all_cons ((refinement204 physical logical agreement).mpr (member204 physical arguments)) (all_cons ((refinement205 physical logical agreement).mpr (member205 physical arguments)) (all_cons ((refinement206 physical logical agreement).mpr (member206 physical arguments)) (all_cons ((refinement207 physical logical agreement).mpr (member207 physical arguments)) (all_cons ((refinement208 physical logical agreement).mpr (member208 physical arguments)) (all_cons ((refinement209 physical logical agreement).mpr (member209 physical arguments)) (all_cons ((refinement210 physical logical agreement).mpr (member210 physical arguments)) (all_cons ((refinement211 physical logical agreement).mpr (member211 physical arguments)) (all_cons ((refinement212 physical logical agreement).mpr (member212 physical arguments)) (all_cons ((refinement213 physical logical agreement).mpr (member213 physical arguments)) (all_cons ((refinement214 physical logical agreement).mpr (member214 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
