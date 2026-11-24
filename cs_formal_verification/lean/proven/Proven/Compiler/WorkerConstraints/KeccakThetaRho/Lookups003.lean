module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Source
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Members000
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Members003
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields000
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups003 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∀ query ∈ queries003, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement48 physical logical agreement).mpr (member48 physical arguments)) (all_cons ((refinement49 physical logical agreement).mpr (member49 physical arguments)) (all_cons ((refinement51 physical logical agreement).mpr (member51 physical arguments)) (all_cons ((refinement0 physical logical agreement).mpr (member0 physical arguments)) (all_cons ((refinement50 physical logical agreement).mpr (member50 physical arguments)) (by intro value member; cases member))))))

end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
