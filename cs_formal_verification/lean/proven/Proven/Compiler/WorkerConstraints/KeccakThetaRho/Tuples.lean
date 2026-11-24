module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries000
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries001
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries002
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries003
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Queries004
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_000 (physical : GKRAddress → F) : List (List F) := [operand1.input.fields physical, operand2.input.fields physical, operand3.input.fields physical, operand4.input.fields physical, operand5.input.fields physical, operand6.input.fields physical, operand7.input.fields physical, operand8.input.fields physical, operand9.input.fields physical, operand10.input.fields physical, operand11.input.fields physical, operand12.input.fields physical, operand13.input.fields physical, operand14.input.fields physical, operand15.input.fields physical, operand16.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_001 (physical : GKRAddress → F) : List (List F) := [operand17.input.fields physical, operand18.input.fields physical, operand19.input.fields physical, operand20.input.fields physical, operand21.input.fields physical, operand22.input.fields physical, operand23.input.fields physical, operand24.input.fields physical, operand25.input.fields physical, operand26.input.fields physical, operand27.input.fields physical, operand28.input.fields physical, operand29.input.fields physical, operand30.input.fields physical, operand31.input.fields physical, operand32.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_002 (physical : GKRAddress → F) : List (List F) := [operand33.input.fields physical, operand34.input.fields physical, operand35.input.fields physical, operand36.input.fields physical, operand37.input.fields physical, operand38.input.fields physical, operand39.input.fields physical, operand40.input.fields physical, operand41.input.fields physical, operand42.input.fields physical, operand43.input.fields physical, operand44.input.fields physical, operand45.input.fields physical, operand46.input.fields physical, operand47.input.fields physical, operand48.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_003 (physical : GKRAddress → F) : List (List F) := [operand49.input.fields physical, operand51.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_000 (physical : GKRAddress → F) : List (List F) := [operand0.input.fields physical, operand50.input.fields physical]

/-- Every complete native tuple, in the selector order of each group. -/
noncomputable def tuples (physical : GKRAddress → F) (group : Fin 3) : List (List F) :=
  ([(tuple0_000 physical ++ (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))), [], (tuple2_000 physical ++ [])] : List (List (List F))).get group

/-- The literal tuples are exactly the actual native requests. -/
theorem binding (physical : GKRAddress → F) (group : Fin 3) :
    NativeLookups.requests (circuitFor .thetaRho) (selectorsFor .thetaRho) physical group = .ok (tuples physical group) := by
  fin_cases group <;> kernel_rfl


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
