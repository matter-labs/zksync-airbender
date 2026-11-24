module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Source
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members010
public import Proven.Compiler.WorkerConstraints.BlakeRound.Members011
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields020
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields021
public import Proven.Compiler.WorkerConstraints.BlakeRound.Fields022

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups005 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.BlakeRound.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∀ query ∈ queries005, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement167 physical logical agreement).mpr (member167 physical arguments)) (all_cons ((refinement168 physical logical agreement).mpr (member168 physical arguments)) (all_cons ((refinement169 physical logical agreement).mpr (member169 physical arguments)) (all_cons ((refinement170 physical logical agreement).mpr (member170 physical arguments)) (all_cons ((refinement171 physical logical agreement).mpr (member171 physical arguments)) (all_cons ((refinement172 physical logical agreement).mpr (member172 physical arguments)) (all_cons ((refinement173 physical logical agreement).mpr (member173 physical arguments)) (all_cons ((refinement174 physical logical agreement).mpr (member174 physical arguments)) (all_cons ((refinement175 physical logical agreement).mpr (member175 physical arguments)) (all_cons ((refinement176 physical logical agreement).mpr (member176 physical arguments)) (all_cons ((refinement177 physical logical agreement).mpr (member177 physical arguments)) (all_cons ((refinement178 physical logical agreement).mpr (member178 physical arguments)) (all_cons ((refinement179 physical logical agreement).mpr (member179 physical arguments)) (all_cons ((refinement180 physical logical agreement).mpr (member180 physical arguments)) (all_cons ((refinement181 physical logical agreement).mpr (member181 physical arguments)) (all_cons ((refinement182 physical logical agreement).mpr (member182 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.BlakeRound
