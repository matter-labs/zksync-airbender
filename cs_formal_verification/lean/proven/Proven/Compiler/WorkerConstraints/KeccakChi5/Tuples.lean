module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Queries000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Queries001
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_000 (physical : GKRAddress → F) : List (List F) := [operand1.input.fields physical, operand2.input.fields physical, operand3.input.fields physical, operand4.input.fields physical, operand5.input.fields physical, operand6.input.fields physical, operand7.input.fields physical, operand8.input.fields physical, operand9.input.fields physical, operand10.input.fields physical, operand11.input.fields physical, operand12.input.fields physical, operand13.input.fields physical, operand14.input.fields physical, operand15.input.fields physical, operand16.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_001 (physical : GKRAddress → F) : List (List F) := [operand17.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_000 (physical : GKRAddress → F) : List (List F) := [operand0.input.fields physical, operand18.input.fields physical]

/-- Every complete native tuple, in the selector order of each group. -/
noncomputable def tuples (physical : GKRAddress → F) (group : Fin 3) : List (List F) :=
  ([(tuple0_000 physical ++ (tuple0_001 physical ++ [])), [], (tuple2_000 physical ++ [])] : List (List (List F))).get group

/-- The literal tuples are exactly the actual native requests. -/
theorem binding (physical : GKRAddress → F) (group : Fin 3) :
    NativeLookups.requests (circuitFor .chi5) (selectorsFor .chi5) physical group = .ok (tuples physical group) := by
  fin_cases group <;> kernel_rfl


end Airbender.Compiler.WorkerConstraints.KeccakChi5
