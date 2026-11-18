module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members000
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members001
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields001
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields002
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups013 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries013, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement14 physical logical agreement).mpr (member14 physical arguments)) (all_cons ((refinement15 physical logical agreement).mpr (member15 physical arguments)) (all_cons ((refinement16 physical logical agreement).mpr (member16 physical arguments)) (all_cons ((refinement17 physical logical agreement).mpr (member17 physical arguments)) (all_cons ((refinement18 physical logical agreement).mpr (member18 physical arguments)) (all_cons ((refinement19 physical logical agreement).mpr (member19 physical arguments)) (all_cons ((refinement20 physical logical agreement).mpr (member20 physical arguments)) (all_cons ((refinement21 physical logical agreement).mpr (member21 physical arguments)) (all_cons ((refinement22 physical logical agreement).mpr (member22 physical arguments)) (all_cons ((refinement23 physical logical agreement).mpr (member23 physical arguments)) (all_cons ((refinement24 physical logical agreement).mpr (member24 physical arguments)) (all_cons ((refinement25 physical logical agreement).mpr (member25 physical arguments)) (all_cons ((refinement26 physical logical agreement).mpr (member26 physical arguments)) (all_cons ((refinement27 physical logical agreement).mpr (member27 physical arguments)) (all_cons ((refinement28 physical logical agreement).mpr (member28 physical arguments)) (all_cons ((refinement29 physical logical agreement).mpr (member29 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
