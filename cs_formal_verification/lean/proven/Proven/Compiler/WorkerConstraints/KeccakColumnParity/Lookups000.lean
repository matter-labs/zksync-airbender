module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Source
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members001
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members002
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members003
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields003
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields004
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields005
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∀ query ∈ queries000, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement50 physical logical agreement).mpr (member50 physical arguments)) (all_cons ((refinement29 physical logical agreement).mpr (member29 physical arguments)) (all_cons ((refinement30 physical logical agreement).mpr (member30 physical arguments)) (all_cons ((refinement31 physical logical agreement).mpr (member31 physical arguments)) (all_cons ((refinement32 physical logical agreement).mpr (member32 physical arguments)) (all_cons ((refinement33 physical logical agreement).mpr (member33 physical arguments)) (all_cons ((refinement34 physical logical agreement).mpr (member34 physical arguments)) (all_cons ((refinement35 physical logical agreement).mpr (member35 physical arguments)) (all_cons ((refinement36 physical logical agreement).mpr (member36 physical arguments)) (all_cons ((refinement37 physical logical agreement).mpr (member37 physical arguments)) (all_cons ((refinement38 physical logical agreement).mpr (member38 physical arguments)) (all_cons ((refinement39 physical logical agreement).mpr (member39 physical arguments)) (all_cons ((refinement40 physical logical agreement).mpr (member40 physical arguments)) (all_cons ((refinement41 physical logical agreement).mpr (member41 physical arguments)) (all_cons ((refinement42 physical logical agreement).mpr (member42 physical arguments)) (all_cons ((refinement43 physical logical agreement).mpr (member43 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
