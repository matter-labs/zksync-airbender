module
public import Proven.Compiler.WorkerConstraints.BlakeG.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeG
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member32 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  kernel_exact native_member (family := .blakeG) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand32.input.fields physical) (List.mem_append_left (a := operand32.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ [])) (List.getElem_mem (l := tuple0_000 physical) (n := 11) (by change 11 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member33 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  kernel_exact native_member (family := .blakeG) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand33.input.fields physical) (List.mem_append_left (a := operand33.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ [])) (List.getElem_mem (l := tuple0_000 physical) (n := 12) (by change 12 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member34 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  kernel_exact native_member (family := .blakeG) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand34.input.fields physical) (List.mem_append_left (a := operand34.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ [])) (List.getElem_mem (l := tuple0_000 physical) (n := 13) (by change 13 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member35 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  kernel_exact native_member (family := .blakeG) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand35.input.fields physical) (List.mem_append_left (a := operand35.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ [])) (List.getElem_mem (l := tuple0_000 physical) (n := 14) (by change 14 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member36 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  kernel_exact native_member (family := .blakeG) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand36.input.fields physical) (List.mem_append_left (a := operand36.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ [])) (List.getElem_mem (l := tuple0_000 physical) (n := 15) (by change 15 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member37 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  kernel_exact native_member (family := .blakeG) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand37.input.fields physical) (List.mem_append_right (b := operand37.input.fields physical) (bs := (tuple0_001 physical ++ [])) (tuple0_000 physical) (List.mem_append_left (a := operand37.input.fields physical) (as := tuple0_001 physical) ([]) (List.getElem_mem (l := tuple0_001 physical) (n := 0) (by change 0 < 3; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member38 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  kernel_exact native_member (family := .blakeG) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand38.input.fields physical) (List.mem_append_right (b := operand38.input.fields physical) (bs := (tuple0_001 physical ++ [])) (tuple0_000 physical) (List.mem_append_left (a := operand38.input.fields physical) (as := tuple0_001 physical) ([]) (List.getElem_mem (l := tuple0_001 physical) (n := 1) (by change 1 < 3; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member39 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeG) (selectorsFor .blakeG) physical (NativeWorkerSetup.rows .blakeG)) :
    ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .blakeG 0 index := by
  kernel_exact native_member (family := .blakeG) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand39.input.fields physical) (List.mem_append_right (b := operand39.input.fields physical) (bs := (tuple0_001 physical ++ [])) (tuple0_000 physical) (List.mem_append_left (a := operand39.input.fields physical) (as := tuple0_001 physical) ([]) (List.getElem_mem (l := tuple0_001 physical) (n := 2) (by change 2 < 3; decide))))


end Airbender.Compiler.WorkerConstraints.BlakeG
