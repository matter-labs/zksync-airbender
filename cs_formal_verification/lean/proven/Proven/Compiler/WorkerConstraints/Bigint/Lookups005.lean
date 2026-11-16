module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Members000
public import Proven.Compiler.WorkerConstraints.Bigint.Members006
public import Proven.Compiler.WorkerConstraints.Bigint.Members007
public import Proven.Compiler.WorkerConstraints.Bigint.Fields001
public import Proven.Compiler.WorkerConstraints.Bigint.Fields012
public import Proven.Compiler.WorkerConstraints.Bigint.Fields013
public import Proven.Compiler.WorkerConstraints.Bigint.Fields014

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies every lookup in this source segment. -/
theorem lookups005 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∀ query ∈ queries005, query.Contains (Verification.environment logical) :=
  (all_cons ((refinement102 physical logical agreement).mpr (member102 physical arguments)) (all_cons ((refinement103 physical logical agreement).mpr (member103 physical arguments)) (all_cons ((refinement104 physical logical agreement).mpr (member104 physical arguments)) (all_cons ((refinement105 physical logical agreement).mpr (member105 physical arguments)) (all_cons ((refinement106 physical logical agreement).mpr (member106 physical arguments)) (all_cons ((refinement107 physical logical agreement).mpr (member107 physical arguments)) (all_cons ((refinement108 physical logical agreement).mpr (member108 physical arguments)) (all_cons ((refinement109 physical logical agreement).mpr (member109 physical arguments)) (all_cons ((refinement110 physical logical agreement).mpr (member110 physical arguments)) (all_cons ((refinement111 physical logical agreement).mpr (member111 physical arguments)) (all_cons ((refinement112 physical logical agreement).mpr (member112 physical arguments)) (all_cons ((refinement113 physical logical agreement).mpr (member113 physical arguments)) (all_cons ((refinement114 physical logical agreement).mpr (member114 physical arguments)) (all_cons ((refinement115 physical logical agreement).mpr (member115 physical arguments)) (all_cons ((refinement116 physical logical agreement).mpr (member116 physical arguments)) (all_cons ((refinement15 physical logical agreement).mpr (member15 physical arguments)) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
