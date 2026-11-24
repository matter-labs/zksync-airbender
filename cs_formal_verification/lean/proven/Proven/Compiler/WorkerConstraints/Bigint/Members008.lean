module
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member128 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand128.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand128.input.fields physical) (List.mem_append_right (b := operand128.input.fields physical) (bs := (tuple1_001 physical ++ [])) (tuple1_000 physical) (List.mem_append_left (a := operand128.input.fields physical) (as := tuple1_001 physical) ([]) (List.getElem_mem (l := tuple1_001 physical) (n := 10) (by change 10 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member129 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand129.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand129.input.fields physical) (List.mem_append_right (b := operand129.input.fields physical) (bs := (tuple1_001 physical ++ [])) (tuple1_000 physical) (List.mem_append_left (a := operand129.input.fields physical) (as := tuple1_001 physical) ([]) (List.getElem_mem (l := tuple1_001 physical) (n := 11) (by change 11 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member130 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand130.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand130.input.fields physical) (List.mem_append_right (b := operand130.input.fields physical) (bs := (tuple1_001 physical ++ [])) (tuple1_000 physical) (List.mem_append_left (a := operand130.input.fields physical) (as := tuple1_001 physical) ([]) (List.getElem_mem (l := tuple1_001 physical) (n := 12) (by change 12 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member131 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand131.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand131.input.fields physical) (List.mem_append_right (b := operand131.input.fields physical) (bs := (tuple1_001 physical ++ [])) (tuple1_000 physical) (List.mem_append_left (a := operand131.input.fields physical) (as := tuple1_001 physical) ([]) (List.getElem_mem (l := tuple1_001 physical) (n := 13) (by change 13 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member132 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand132.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand132.input.fields physical) (List.mem_append_right (b := operand132.input.fields physical) (bs := (tuple1_001 physical ++ [])) (tuple1_000 physical) (List.mem_append_left (a := operand132.input.fields physical) (as := tuple1_001 physical) ([]) (List.getElem_mem (l := tuple1_001 physical) (n := 14) (by change 14 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member133 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand133.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand133.input.fields physical) (List.mem_append_right (b := operand133.input.fields physical) (bs := (tuple1_001 physical ++ [])) (tuple1_000 physical) (List.mem_append_left (a := operand133.input.fields physical) (as := tuple1_001 physical) ([]) (List.getElem_mem (l := tuple1_001 physical) (n := 15) (by change 15 < 16; decide))))


end Airbender.Compiler.WorkerConstraints.Bigint
