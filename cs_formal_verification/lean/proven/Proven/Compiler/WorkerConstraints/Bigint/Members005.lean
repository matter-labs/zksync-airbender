module
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member80 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand80.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand80.input.fields physical) (List.mem_append_right (b := operand80.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand80.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 8) (by change 8 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member81 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand81.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand81.input.fields physical) (List.mem_append_right (b := operand81.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand81.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 9) (by change 9 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member82 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand82.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand82.input.fields physical) (List.mem_append_right (b := operand82.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand82.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 10) (by change 10 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member83 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand83.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand83.input.fields physical) (List.mem_append_right (b := operand83.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand83.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 11) (by change 11 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member84 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand84.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand84.input.fields physical) (List.mem_append_right (b := operand84.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand84.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 12) (by change 12 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member85 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand85.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand85.input.fields physical) (List.mem_append_right (b := operand85.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand85.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 13) (by change 13 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member86 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand86.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand86.input.fields physical) (List.mem_append_right (b := operand86.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand86.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 14) (by change 14 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member87 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand87.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand87.input.fields physical) (List.mem_append_right (b := operand87.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand87.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 15) (by change 15 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member88 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand88.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand88.input.fields physical) (List.mem_append_right (b := operand88.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand88.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand88.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 0) (by change 0 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member89 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand89.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand89.input.fields physical) (List.mem_append_right (b := operand89.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand89.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand89.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 1) (by change 1 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member90 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand90.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand90.input.fields physical) (List.mem_append_right (b := operand90.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand90.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand90.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 2) (by change 2 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member91 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand91.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand91.input.fields physical) (List.mem_append_right (b := operand91.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand91.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand91.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 3) (by change 3 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member92 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand92.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand92.input.fields physical) (List.mem_append_right (b := operand92.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand92.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand92.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 4) (by change 4 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member93 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand93.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand93.input.fields physical) (List.mem_append_right (b := operand93.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand93.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand93.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 5) (by change 5 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member94 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand94.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand94.input.fields physical) (List.mem_append_right (b := operand94.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand94.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand94.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 6) (by change 6 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member95 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand95.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand95.input.fields physical) (List.mem_append_right (b := operand95.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand95.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand95.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 7) (by change 7 < 16; decide)))))


end Airbender.Compiler.WorkerConstraints.Bigint
