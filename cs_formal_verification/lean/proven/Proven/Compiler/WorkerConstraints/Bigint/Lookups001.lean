module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Members007
public import Proven.Compiler.WorkerConstraints.Bigint.Members008
public import Proven.Compiler.WorkerConstraints.Bigint.Fields014
public import Proven.Compiler.WorkerConstraints.Bigint.Fields015
public import Proven.Compiler.WorkerConstraints.Bigint.Fields016

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∀ query ∈ queries001, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement117 physical logical agreement).mpr (member117 physical arguments)) (all_cons ((refinement118 physical logical agreement).mpr (member118 physical arguments)) (all_cons ((refinement119 physical logical agreement).mpr (member119 physical arguments)) (all_cons ((refinement120 physical logical agreement).mpr (member120 physical arguments)) (all_cons ((refinement121 physical logical agreement).mpr (member121 physical arguments)) (all_cons ((refinement122 physical logical agreement).mpr (member122 physical arguments)) (all_cons ((refinement123 physical logical agreement).mpr (member123 physical arguments)) (all_cons ((refinement124 physical logical agreement).mpr (member124 physical arguments)) (all_cons ((refinement125 physical logical agreement).mpr (member125 physical arguments)) (all_cons ((refinement126 physical logical agreement).mpr (member126 physical arguments)) (all_cons ((refinement127 physical logical agreement).mpr (member127 physical arguments)) (all_cons ((refinement128 physical logical agreement).mpr (member128 physical arguments)) (all_cons ((refinement129 physical logical agreement).mpr (member129 physical arguments)) (all_cons ((refinement130 physical logical agreement).mpr (member130 physical arguments)) (all_cons ((refinement131 physical logical agreement).mpr (member131 physical arguments)) (all_cons ((refinement132 physical logical agreement).mpr (member132 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
