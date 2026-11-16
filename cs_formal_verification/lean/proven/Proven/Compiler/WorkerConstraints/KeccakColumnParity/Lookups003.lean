module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Source
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members001
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members003
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields003
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups003 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∀ query ∈ queries003, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement25 physical logical agreement).mpr (member25 physical arguments)) (all_cons ((refinement26 physical logical agreement).mpr (member26 physical arguments)) (all_cons ((refinement27 physical logical agreement).mpr (member27 physical arguments)) (all_cons ((refinement28 physical logical agreement).mpr (member28 physical arguments)) (all_cons ((refinement50 physical logical agreement).mpr (member50 physical arguments)) (by intro value member; cases member))))))

end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
