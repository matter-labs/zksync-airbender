module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Source
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members000
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members002
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members003
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields000
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields001
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields005
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∀ query ∈ queries001, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement44 physical logical agreement).mpr (member44 physical arguments)) (all_cons ((refinement45 physical logical agreement).mpr (member45 physical arguments)) (all_cons ((refinement46 physical logical agreement).mpr (member46 physical arguments)) (all_cons ((refinement47 physical logical agreement).mpr (member47 physical arguments)) (all_cons ((refinement48 physical logical agreement).mpr (member48 physical arguments)) (all_cons ((refinement49 physical logical agreement).mpr (member49 physical arguments)) (all_cons ((refinement51 physical logical agreement).mpr (member51 physical arguments)) (all_cons ((refinement0 physical logical agreement).mpr (member0 physical arguments)) (all_cons ((refinement1 physical logical agreement).mpr (member1 physical arguments)) (all_cons ((refinement2 physical logical agreement).mpr (member2 physical arguments)) (all_cons ((refinement3 physical logical agreement).mpr (member3 physical arguments)) (all_cons ((refinement4 physical logical agreement).mpr (member4 physical arguments)) (all_cons ((refinement5 physical logical agreement).mpr (member5 physical arguments)) (all_cons ((refinement6 physical logical agreement).mpr (member6 physical arguments)) (all_cons ((refinement7 physical logical agreement).mpr (member7 physical arguments)) (all_cons ((refinement8 physical logical agreement).mpr (member8 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
