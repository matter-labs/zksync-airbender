module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries000
public import Proven.Compiler.WorkerConstraints.Bigint.Queries001
public import Proven.Compiler.WorkerConstraints.Bigint.Queries002
public import Proven.Compiler.WorkerConstraints.Bigint.Queries003
public import Proven.Compiler.WorkerConstraints.Bigint.Queries004
public import Proven.Compiler.WorkerConstraints.Bigint.Queries005
public import Proven.Compiler.WorkerConstraints.Bigint.Queries006
public import Proven.Compiler.WorkerConstraints.Bigint.Queries007
public import Proven.Compiler.WorkerConstraints.Bigint.Queries008
public import Proven.Compiler.WorkerConstraints.Bigint.Queries009
public import Proven.Compiler.WorkerConstraints.Bigint.Queries010
public import Proven.Compiler.WorkerConstraints.Bigint.Queries011
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_000 (physical : GKRAddress → F) : List (List F) := [operand56.input.fields physical, operand57.input.fields physical, operand58.input.fields physical, operand59.input.fields physical, operand60.input.fields physical, operand61.input.fields physical, operand62.input.fields physical, operand63.input.fields physical, operand64.input.fields physical, operand65.input.fields physical, operand66.input.fields physical, operand67.input.fields physical, operand68.input.fields physical, operand69.input.fields physical, operand70.input.fields physical, operand71.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_001 (physical : GKRAddress → F) : List (List F) := [operand72.input.fields physical, operand73.input.fields physical, operand74.input.fields physical, operand75.input.fields physical, operand76.input.fields physical, operand77.input.fields physical, operand78.input.fields physical, operand79.input.fields physical, operand80.input.fields physical, operand81.input.fields physical, operand82.input.fields physical, operand83.input.fields physical, operand84.input.fields physical, operand85.input.fields physical, operand86.input.fields physical, operand87.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_002 (physical : GKRAddress → F) : List (List F) := [operand88.input.fields physical, operand89.input.fields physical, operand90.input.fields physical, operand91.input.fields physical, operand92.input.fields physical, operand93.input.fields physical, operand94.input.fields physical, operand95.input.fields physical, operand96.input.fields physical, operand97.input.fields physical, operand98.input.fields physical, operand99.input.fields physical, operand100.input.fields physical, operand101.input.fields physical, operand102.input.fields physical, operand103.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_003 (physical : GKRAddress → F) : List (List F) := [operand104.input.fields physical, operand105.input.fields physical, operand106.input.fields physical, operand107.input.fields physical, operand108.input.fields physical, operand109.input.fields physical, operand110.input.fields physical, operand111.input.fields physical, operand112.input.fields physical, operand113.input.fields physical, operand114.input.fields physical, operand115.input.fields physical, operand116.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple1_000 (physical : GKRAddress → F) : List (List F) := [operand0.input.fields physical, operand1.input.fields physical, operand2.input.fields physical, operand3.input.fields physical, operand4.input.fields physical, operand5.input.fields physical, operand6.input.fields physical, operand7.input.fields physical, operand8.input.fields physical, operand9.input.fields physical, operand10.input.fields physical, operand11.input.fields physical, operand12.input.fields physical, operand13.input.fields physical, operand14.input.fields physical, operand117.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple1_001 (physical : GKRAddress → F) : List (List F) := [operand118.input.fields physical, operand119.input.fields physical, operand120.input.fields physical, operand121.input.fields physical, operand122.input.fields physical, operand123.input.fields physical, operand124.input.fields physical, operand125.input.fields physical, operand126.input.fields physical, operand127.input.fields physical, operand128.input.fields physical, operand129.input.fields physical, operand130.input.fields physical, operand131.input.fields physical, operand132.input.fields physical, operand133.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_000 (physical : GKRAddress → F) : List (List F) := [operand15.input.fields physical, operand16.input.fields physical, operand17.input.fields physical, operand18.input.fields physical, operand19.input.fields physical, operand20.input.fields physical, operand21.input.fields physical, operand22.input.fields physical, operand23.input.fields physical, operand24.input.fields physical, operand25.input.fields physical, operand26.input.fields physical, operand27.input.fields physical, operand28.input.fields physical, operand29.input.fields physical, operand30.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_001 (physical : GKRAddress → F) : List (List F) := [operand31.input.fields physical, operand32.input.fields physical, operand33.input.fields physical, operand34.input.fields physical, operand35.input.fields physical, operand36.input.fields physical, operand37.input.fields physical, operand38.input.fields physical, operand39.input.fields physical, operand40.input.fields physical, operand41.input.fields physical, operand42.input.fields physical, operand43.input.fields physical, operand44.input.fields physical, operand45.input.fields physical, operand46.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_002 (physical : GKRAddress → F) : List (List F) := [operand47.input.fields physical, operand48.input.fields physical, operand49.input.fields physical, operand50.input.fields physical, operand51.input.fields physical, operand52.input.fields physical, operand53.input.fields physical, operand54.input.fields physical, operand55.input.fields physical]

/-- Every complete native tuple, in the selector order of each group. -/
noncomputable def tuples (physical : GKRAddress → F) (group : Fin 3) : List (List F) :=
  ([(tuple0_000 physical ++ (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))), (tuple1_000 physical ++ (tuple1_001 physical ++ [])), (tuple2_000 physical ++ (tuple2_001 physical ++ (tuple2_002 physical ++ [])))] : List (List (List F))).get group

/-- The literal tuples are exactly the actual native requests. -/
theorem binding (physical : GKRAddress → F) (group : Fin 3) :
    NativeLookups.requests (circuitFor .bigint) (selectorsFor .bigint) physical group = .ok (tuples physical group) := by
  fin_cases group <;> kernel_rfl


end Airbender.Compiler.WorkerConstraints.Bigint
