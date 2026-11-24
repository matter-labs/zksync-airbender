module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members009
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members010
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields018
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields019
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields020

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups004 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries004, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement151 physical logical agreement).mpr (member151 physical arguments)) (all_cons ((refinement152 physical logical agreement).mpr (member152 physical arguments)) (all_cons ((refinement153 physical logical agreement).mpr (member153 physical arguments)) (all_cons ((refinement154 physical logical agreement).mpr (member154 physical arguments)) (all_cons ((refinement155 physical logical agreement).mpr (member155 physical arguments)) (all_cons ((refinement156 physical logical agreement).mpr (member156 physical arguments)) (all_cons ((refinement157 physical logical agreement).mpr (member157 physical arguments)) (all_cons ((refinement158 physical logical agreement).mpr (member158 physical arguments)) (all_cons ((refinement159 physical logical agreement).mpr (member159 physical arguments)) (all_cons ((refinement160 physical logical agreement).mpr (member160 physical arguments)) (all_cons ((refinement161 physical logical agreement).mpr (member161 physical arguments)) (all_cons ((refinement162 physical logical agreement).mpr (member162 physical arguments)) (all_cons ((refinement163 physical logical agreement).mpr (member163 physical arguments)) (all_cons ((refinement164 physical logical agreement).mpr (member164 physical arguments)) (all_cons ((refinement165 physical logical agreement).mpr (member165 physical arguments)) (all_cons ((refinement166 physical logical agreement).mpr (member166 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
