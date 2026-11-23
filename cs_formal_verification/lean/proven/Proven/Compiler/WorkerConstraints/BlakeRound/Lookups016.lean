module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members003
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members004
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields007
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields008
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields009

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups016 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries016, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement62 physical logical agreement).mpr (member62 physical arguments)) (all_cons ((refinement63 physical logical agreement).mpr (member63 physical arguments)) (all_cons ((refinement64 physical logical agreement).mpr (member64 physical arguments)) (all_cons ((refinement65 physical logical agreement).mpr (member65 physical arguments)) (all_cons ((refinement66 physical logical agreement).mpr (member66 physical arguments)) (all_cons ((refinement67 physical logical agreement).mpr (member67 physical arguments)) (all_cons ((refinement68 physical logical agreement).mpr (member68 physical arguments)) (all_cons ((refinement69 physical logical agreement).mpr (member69 physical arguments)) (all_cons ((refinement70 physical logical agreement).mpr (member70 physical arguments)) (all_cons ((refinement71 physical logical agreement).mpr (member71 physical arguments)) (all_cons ((refinement72 physical logical agreement).mpr (member72 physical arguments)) (all_cons ((refinement73 physical logical agreement).mpr (member73 physical arguments)) (all_cons ((refinement74 physical logical agreement).mpr (member74 physical arguments)) (all_cons ((refinement75 physical logical agreement).mpr (member75 physical arguments)) (all_cons ((refinement76 physical logical agreement).mpr (member76 physical arguments)) (all_cons ((refinement77 physical logical agreement).mpr (member77 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
