module
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member0 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand0.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand0.input.fields physical) (List.mem_append_left (a := operand0.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 0) (by change 0 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member1 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand1.input.fields physical) (List.mem_append_left (a := operand1.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 1) (by change 1 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member2 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand2.input.fields physical) (List.mem_append_left (a := operand2.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 2) (by change 2 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member3 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand3.input.fields physical) (List.mem_append_left (a := operand3.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 3) (by change 3 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member4 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand4.input.fields physical) (List.mem_append_left (a := operand4.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 4) (by change 4 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member5 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand5.input.fields physical) (List.mem_append_left (a := operand5.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 5) (by change 5 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member6 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand6.input.fields physical) (List.mem_append_left (a := operand6.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 6) (by change 6 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member7 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand7.input.fields physical) (List.mem_append_left (a := operand7.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 7) (by change 7 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member8 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand8.input.fields physical) (List.mem_append_left (a := operand8.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 8) (by change 8 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member9 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand9.input.fields physical) (List.mem_append_left (a := operand9.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 9) (by change 9 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member10 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand10.input.fields physical) (List.mem_append_left (a := operand10.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 10) (by change 10 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member11 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand11.input.fields physical) (List.mem_append_left (a := operand11.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 11) (by change 11 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member12 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand12.input.fields physical) (List.mem_append_left (a := operand12.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 12) (by change 12 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member13 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand13.input.fields physical) (List.mem_append_left (a := operand13.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 13) (by change 13 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member14 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 1) (values := operand14.input.fields physical) (List.mem_append_left (a := operand14.input.fields physical) (as := tuple1_000 physical) ((tuple1_001 physical ++ [])) (List.getElem_mem (l := tuple1_000 physical) (n := 14) (by change 14 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member15 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand15.input.fields physical) (List.mem_append_left (a := operand15.input.fields physical) (as := tuple2_000 physical) ((tuple2_001 physical ++ (tuple2_002 physical ++ []))) (List.getElem_mem (l := tuple2_000 physical) (n := 0) (by change 0 < 16; decide)))


end Airbender.Compiler.WorkerConstraints.Bigint
