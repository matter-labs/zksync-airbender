module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Source
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Members000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Members001
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Fields000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Fields001
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Fields002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakChi5.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .chi5) (selectorsFor .chi5) physical (NativeWorkerSetup.rows .chi5)) :
    ∀ query ∈ queries000, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement18 physical logical agreement).mpr (member18 physical arguments)) (all_cons ((refinement1 physical logical agreement).mpr (member1 physical arguments)) (all_cons ((refinement2 physical logical agreement).mpr (member2 physical arguments)) (all_cons ((refinement3 physical logical agreement).mpr (member3 physical arguments)) (all_cons ((refinement4 physical logical agreement).mpr (member4 physical arguments)) (all_cons ((refinement5 physical logical agreement).mpr (member5 physical arguments)) (all_cons ((refinement6 physical logical agreement).mpr (member6 physical arguments)) (all_cons ((refinement7 physical logical agreement).mpr (member7 physical arguments)) (all_cons ((refinement8 physical logical agreement).mpr (member8 physical arguments)) (all_cons ((refinement9 physical logical agreement).mpr (member9 physical arguments)) (all_cons ((refinement10 physical logical agreement).mpr (member10 physical arguments)) (all_cons ((refinement11 physical logical agreement).mpr (member11 physical arguments)) (all_cons ((refinement12 physical logical agreement).mpr (member12 physical arguments)) (all_cons ((refinement13 physical logical agreement).mpr (member13 physical arguments)) (all_cons ((refinement14 physical logical agreement).mpr (member14 physical arguments)) (all_cons ((refinement15 physical logical agreement).mpr (member15 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakChi5
