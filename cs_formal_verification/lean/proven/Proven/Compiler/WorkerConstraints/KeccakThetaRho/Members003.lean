module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member48 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand48.input.fields physical) (List.mem_append_right (b := operand48.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand48.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand48.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 15) (by change 15 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member49 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand49.input.fields physical) (List.mem_append_right (b := operand49.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand49.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_right (b := operand49.input.fields physical) (bs := (tuple0_003 physical ++ [])) (tuple0_002 physical) (List.mem_append_left (a := operand49.input.fields physical) (as := tuple0_003 physical) ([]) (List.getElem_mem (l := tuple0_003 physical) (n := 0) (by change 0 < 2; decide))))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member50 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .thetaRho 2 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand50.input.fields physical) (List.mem_append_left (a := operand50.input.fields physical) (as := tuple2_000 physical) ([]) (List.getElem_mem (l := tuple2_000 physical) (n := 1) (by change 1 < 2; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member51 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand51.input.fields physical) (List.mem_append_right (b := operand51.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand51.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_right (b := operand51.input.fields physical) (bs := (tuple0_003 physical ++ [])) (tuple0_002 physical) (List.mem_append_left (a := operand51.input.fields physical) (as := tuple0_003 physical) ([]) (List.getElem_mem (l := tuple0_003 physical) (n := 1) (by change 1 < 2; decide))))))


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
