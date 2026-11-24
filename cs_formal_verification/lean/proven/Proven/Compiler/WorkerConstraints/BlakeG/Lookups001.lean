module
public import Proven.Compiler.WorkerConstraints.BlakeG.Source
public import Proven.Compiler.WorkerConstraints.BlakeG.Members000
public import Proven.Compiler.WorkerConstraints.BlakeG.Members002
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields000
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields001
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields004

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∀ query ∈ queries001, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement35 physical logical agreement).mpr (member35 physical arguments)) (all_cons ((refinement36 physical logical agreement).mpr (member36 physical arguments)) (all_cons ((refinement37 physical logical agreement).mpr (member37 physical arguments)) (all_cons ((refinement38 physical logical agreement).mpr (member38 physical arguments)) (all_cons ((refinement39 physical logical agreement).mpr (member39 physical arguments)) (all_cons ((refinement0 physical logical agreement).mpr (member0 physical arguments)) (all_cons ((refinement1 physical logical agreement).mpr (member1 physical arguments)) (all_cons ((refinement2 physical logical agreement).mpr (member2 physical arguments)) (all_cons ((refinement3 physical logical agreement).mpr (member3 physical arguments)) (all_cons ((refinement4 physical logical agreement).mpr (member4 physical arguments)) (all_cons ((refinement5 physical logical agreement).mpr (member5 physical arguments)) (all_cons ((refinement6 physical logical agreement).mpr (member6 physical arguments)) (all_cons ((refinement7 physical logical agreement).mpr (member7 physical arguments)) (all_cons ((refinement8 physical logical agreement).mpr (member8 physical arguments)) (all_cons ((refinement9 physical logical agreement).mpr (member9 physical arguments)) (all_cons ((refinement10 physical logical agreement).mpr (member10 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeG
