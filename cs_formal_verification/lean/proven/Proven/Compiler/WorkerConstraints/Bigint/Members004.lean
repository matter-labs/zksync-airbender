module
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member64 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand64.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand64.input.fields physical) (List.mem_append_left (a := operand64.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 8) (by change 8 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member65 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand65.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand65.input.fields physical) (List.mem_append_left (a := operand65.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 9) (by change 9 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member66 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand66.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand66.input.fields physical) (List.mem_append_left (a := operand66.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 10) (by change 10 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member67 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand67.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand67.input.fields physical) (List.mem_append_left (a := operand67.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 11) (by change 11 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member68 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand68.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand68.input.fields physical) (List.mem_append_left (a := operand68.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 12) (by change 12 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member69 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand69.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand69.input.fields physical) (List.mem_append_left (a := operand69.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 13) (by change 13 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member70 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand70.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand70.input.fields physical) (List.mem_append_left (a := operand70.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 14) (by change 14 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member71 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand71.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand71.input.fields physical) (List.mem_append_left (a := operand71.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 15) (by change 15 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member72 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand72.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand72.input.fields physical) (List.mem_append_right (b := operand72.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand72.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 0) (by change 0 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member73 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand73.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand73.input.fields physical) (List.mem_append_right (b := operand73.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand73.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 1) (by change 1 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member74 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand74.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand74.input.fields physical) (List.mem_append_right (b := operand74.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand74.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 2) (by change 2 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member75 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand75.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand75.input.fields physical) (List.mem_append_right (b := operand75.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand75.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 3) (by change 3 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member76 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand76.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand76.input.fields physical) (List.mem_append_right (b := operand76.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand76.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 4) (by change 4 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member77 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand77.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand77.input.fields physical) (List.mem_append_right (b := operand77.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand77.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 5) (by change 5 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member78 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand78.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand78.input.fields physical) (List.mem_append_right (b := operand78.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand78.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 6) (by change 6 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member79 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand79.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand79.input.fields physical) (List.mem_append_right (b := operand79.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand79.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 7) (by change 7 < 16; decide))))


end Airbender.Compiler.WorkerConstraints.Bigint
