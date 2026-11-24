module
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member48 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand48.input.fields physical) (List.mem_append_right (b := operand48.input.fields physical) (bs := (tuple2_001 physical ++ (tuple2_002 physical ++ []))) (tuple2_000 physical) (List.mem_append_right (b := operand48.input.fields physical) (bs := (tuple2_002 physical ++ [])) (tuple2_001 physical) (List.mem_append_left (a := operand48.input.fields physical) (as := tuple2_002 physical) ([]) (List.getElem_mem (l := tuple2_002 physical) (n := 1) (by change 1 < 9; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member49 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand49.input.fields physical) (List.mem_append_right (b := operand49.input.fields physical) (bs := (tuple2_001 physical ++ (tuple2_002 physical ++ []))) (tuple2_000 physical) (List.mem_append_right (b := operand49.input.fields physical) (bs := (tuple2_002 physical ++ [])) (tuple2_001 physical) (List.mem_append_left (a := operand49.input.fields physical) (as := tuple2_002 physical) ([]) (List.getElem_mem (l := tuple2_002 physical) (n := 2) (by change 2 < 9; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member50 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand50.input.fields physical) (List.mem_append_right (b := operand50.input.fields physical) (bs := (tuple2_001 physical ++ (tuple2_002 physical ++ []))) (tuple2_000 physical) (List.mem_append_right (b := operand50.input.fields physical) (bs := (tuple2_002 physical ++ [])) (tuple2_001 physical) (List.mem_append_left (a := operand50.input.fields physical) (as := tuple2_002 physical) ([]) (List.getElem_mem (l := tuple2_002 physical) (n := 3) (by change 3 < 9; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member51 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand51.input.fields physical) (List.mem_append_right (b := operand51.input.fields physical) (bs := (tuple2_001 physical ++ (tuple2_002 physical ++ []))) (tuple2_000 physical) (List.mem_append_right (b := operand51.input.fields physical) (bs := (tuple2_002 physical ++ [])) (tuple2_001 physical) (List.mem_append_left (a := operand51.input.fields physical) (as := tuple2_002 physical) ([]) (List.getElem_mem (l := tuple2_002 physical) (n := 4) (by change 4 < 9; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member52 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand52.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand52.input.fields physical) (List.mem_append_right (b := operand52.input.fields physical) (bs := (tuple2_001 physical ++ (tuple2_002 physical ++ []))) (tuple2_000 physical) (List.mem_append_right (b := operand52.input.fields physical) (bs := (tuple2_002 physical ++ [])) (tuple2_001 physical) (List.mem_append_left (a := operand52.input.fields physical) (as := tuple2_002 physical) ([]) (List.getElem_mem (l := tuple2_002 physical) (n := 5) (by change 5 < 9; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member53 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand53.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand53.input.fields physical) (List.mem_append_right (b := operand53.input.fields physical) (bs := (tuple2_001 physical ++ (tuple2_002 physical ++ []))) (tuple2_000 physical) (List.mem_append_right (b := operand53.input.fields physical) (bs := (tuple2_002 physical ++ [])) (tuple2_001 physical) (List.mem_append_left (a := operand53.input.fields physical) (as := tuple2_002 physical) ([]) (List.getElem_mem (l := tuple2_002 physical) (n := 6) (by change 6 < 9; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member54 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand54.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand54.input.fields physical) (List.mem_append_right (b := operand54.input.fields physical) (bs := (tuple2_001 physical ++ (tuple2_002 physical ++ []))) (tuple2_000 physical) (List.mem_append_right (b := operand54.input.fields physical) (bs := (tuple2_002 physical ++ [])) (tuple2_001 physical) (List.mem_append_left (a := operand54.input.fields physical) (as := tuple2_002 physical) ([]) (List.getElem_mem (l := tuple2_002 physical) (n := 7) (by change 7 < 9; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member55 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand55.input.fields physical = NativeWorkerSetup.rows .bigint 2 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand55.input.fields physical) (List.mem_append_right (b := operand55.input.fields physical) (bs := (tuple2_001 physical ++ (tuple2_002 physical ++ []))) (tuple2_000 physical) (List.mem_append_right (b := operand55.input.fields physical) (bs := (tuple2_002 physical ++ [])) (tuple2_001 physical) (List.mem_append_left (a := operand55.input.fields physical) (as := tuple2_002 physical) ([]) (List.getElem_mem (l := tuple2_002 physical) (n := 8) (by change 8 < 9; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member56 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand56.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand56.input.fields physical) (List.mem_append_left (a := operand56.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 0) (by change 0 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member57 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand57.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand57.input.fields physical) (List.mem_append_left (a := operand57.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 1) (by change 1 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member58 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand58.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand58.input.fields physical) (List.mem_append_left (a := operand58.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 2) (by change 2 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member59 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand59.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand59.input.fields physical) (List.mem_append_left (a := operand59.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 3) (by change 3 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member60 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand60.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand60.input.fields physical) (List.mem_append_left (a := operand60.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 4) (by change 4 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member61 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand61.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand61.input.fields physical) (List.mem_append_left (a := operand61.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 5) (by change 5 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member62 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand62.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand62.input.fields physical) (List.mem_append_left (a := operand62.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 6) (by change 6 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member63 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .bigint) (selectorsFor .bigint) physical (NativeWorkerSetup.rows .bigint)) :
    ∃ index, operand63.input.fields physical = NativeWorkerSetup.rows .bigint 0 index := by
  kernel_exact native_member (family := .bigint) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand63.input.fields physical) (List.mem_append_left (a := operand63.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (List.getElem_mem (l := tuple0_000 physical) (n := 7) (by change 7 < 16; decide)))


end Airbender.Compiler.WorkerConstraints.Bigint
