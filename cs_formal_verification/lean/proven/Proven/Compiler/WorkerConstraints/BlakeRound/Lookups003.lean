module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members008
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members009
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields016
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields017
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields018

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups003 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries003, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement135 physical logical agreement).mpr (member135 physical arguments)) (all_cons ((refinement136 physical logical agreement).mpr (member136 physical arguments)) (all_cons ((refinement137 physical logical agreement).mpr (member137 physical arguments)) (all_cons ((refinement138 physical logical agreement).mpr (member138 physical arguments)) (all_cons ((refinement139 physical logical agreement).mpr (member139 physical arguments)) (all_cons ((refinement140 physical logical agreement).mpr (member140 physical arguments)) (all_cons ((refinement141 physical logical agreement).mpr (member141 physical arguments)) (all_cons ((refinement142 physical logical agreement).mpr (member142 physical arguments)) (all_cons ((refinement143 physical logical agreement).mpr (member143 physical arguments)) (all_cons ((refinement144 physical logical agreement).mpr (member144 physical arguments)) (all_cons ((refinement145 physical logical agreement).mpr (member145 physical arguments)) (all_cons ((refinement146 physical logical agreement).mpr (member146 physical arguments)) (all_cons ((refinement147 physical logical agreement).mpr (member147 physical arguments)) (all_cons ((refinement148 physical logical agreement).mpr (member148 physical arguments)) (all_cons ((refinement149 physical logical agreement).mpr (member149 physical arguments)) (all_cons ((refinement150 physical logical agreement).mpr (member150 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
