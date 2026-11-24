module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Source
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members000
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Members001
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields001
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields002
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Fields003

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups002 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakColumnParity.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∀ query ∈ queries002, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement9 physical logical agreement).mpr (member9 physical arguments)) (all_cons ((refinement10 physical logical agreement).mpr (member10 physical arguments)) (all_cons ((refinement11 physical logical agreement).mpr (member11 physical arguments)) (all_cons ((refinement12 physical logical agreement).mpr (member12 physical arguments)) (all_cons ((refinement13 physical logical agreement).mpr (member13 physical arguments)) (all_cons ((refinement14 physical logical agreement).mpr (member14 physical arguments)) (all_cons ((refinement15 physical logical agreement).mpr (member15 physical arguments)) (all_cons ((refinement16 physical logical agreement).mpr (member16 physical arguments)) (all_cons ((refinement17 physical logical agreement).mpr (member17 physical arguments)) (all_cons ((refinement18 physical logical agreement).mpr (member18 physical arguments)) (all_cons ((refinement19 physical logical agreement).mpr (member19 physical arguments)) (all_cons ((refinement20 physical logical agreement).mpr (member20 physical arguments)) (all_cons ((refinement21 physical logical agreement).mpr (member21 physical arguments)) (all_cons ((refinement22 physical logical agreement).mpr (member22 physical arguments)) (all_cons ((refinement23 physical logical agreement).mpr (member23 physical arguments)) (all_cons ((refinement24 physical logical agreement).mpr (member24 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
