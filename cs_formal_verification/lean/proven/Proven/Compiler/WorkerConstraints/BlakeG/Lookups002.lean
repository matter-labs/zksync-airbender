module
public import Proven.Compiler.WorkerConstraints.BlakeG.Source
public import Proven.Compiler.WorkerConstraints.BlakeG.Members000
public import Proven.Compiler.WorkerConstraints.BlakeG.Members001
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields001
public import Proven.Compiler.WorkerConstraints.BlakeG.Fields002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups002 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeG.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∀ query ∈ queries002, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement11 physical logical agreement).mpr (member11 physical arguments)) (all_cons ((refinement12 physical logical agreement).mpr (member12 physical arguments)) (all_cons ((refinement13 physical logical agreement).mpr (member13 physical arguments)) (all_cons ((refinement14 physical logical agreement).mpr (member14 physical arguments)) (all_cons ((refinement15 physical logical agreement).mpr (member15 physical arguments)) (all_cons ((refinement16 physical logical agreement).mpr (member16 physical arguments)) (all_cons ((refinement17 physical logical agreement).mpr (member17 physical arguments)) (all_cons ((refinement18 physical logical agreement).mpr (member18 physical arguments)) (all_cons ((refinement19 physical logical agreement).mpr (member19 physical arguments)) (all_cons ((refinement20 physical logical agreement).mpr (member20 physical arguments)) (by intro value member; cases member)))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeG
