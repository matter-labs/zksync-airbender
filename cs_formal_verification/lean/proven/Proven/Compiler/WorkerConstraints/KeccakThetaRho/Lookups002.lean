module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Source
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Members002
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields004
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields005

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups002 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∀ query ∈ queries002, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement32 physical logical agreement).mpr (member32 physical arguments)) (all_cons ((refinement33 physical logical agreement).mpr (member33 physical arguments)) (all_cons ((refinement34 physical logical agreement).mpr (member34 physical arguments)) (all_cons ((refinement35 physical logical agreement).mpr (member35 physical arguments)) (all_cons ((refinement36 physical logical agreement).mpr (member36 physical arguments)) (all_cons ((refinement37 physical logical agreement).mpr (member37 physical arguments)) (all_cons ((refinement38 physical logical agreement).mpr (member38 physical arguments)) (all_cons ((refinement39 physical logical agreement).mpr (member39 physical arguments)) (all_cons ((refinement40 physical logical agreement).mpr (member40 physical arguments)) (all_cons ((refinement41 physical logical agreement).mpr (member41 physical arguments)) (all_cons ((refinement42 physical logical agreement).mpr (member42 physical arguments)) (all_cons ((refinement43 physical logical agreement).mpr (member43 physical arguments)) (all_cons ((refinement44 physical logical agreement).mpr (member44 physical arguments)) (all_cons ((refinement45 physical logical agreement).mpr (member45 physical arguments)) (all_cons ((refinement46 physical logical agreement).mpr (member46 physical arguments)) (all_cons ((refinement47 physical logical agreement).mpr (member47 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
