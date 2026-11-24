module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member16 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand16.input.fields physical) (List.mem_append_right (b := operand16.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand16.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 0) (by change 0 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member17 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand17.input.fields physical) (List.mem_append_right (b := operand17.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand17.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 1) (by change 1 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member18 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand18.input.fields physical) (List.mem_append_right (b := operand18.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand18.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 2) (by change 2 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member19 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand19.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand19.input.fields physical) (List.mem_append_right (b := operand19.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand19.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 3) (by change 3 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member20 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand20.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand20.input.fields physical) (List.mem_append_right (b := operand20.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand20.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 4) (by change 4 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member21 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand21.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand21.input.fields physical) (List.mem_append_right (b := operand21.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand21.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 5) (by change 5 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member22 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand22.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand22.input.fields physical) (List.mem_append_right (b := operand22.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand22.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 6) (by change 6 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member23 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand23.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand23.input.fields physical) (List.mem_append_right (b := operand23.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand23.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 7) (by change 7 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member24 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand24.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand24.input.fields physical) (List.mem_append_right (b := operand24.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand24.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 8) (by change 8 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member25 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand25.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand25.input.fields physical) (List.mem_append_right (b := operand25.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand25.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 9) (by change 9 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member26 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand26.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand26.input.fields physical) (List.mem_append_right (b := operand26.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand26.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 10) (by change 10 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member27 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand27.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand27.input.fields physical) (List.mem_append_right (b := operand27.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand27.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 11) (by change 11 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member28 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand28.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand28.input.fields physical) (List.mem_append_right (b := operand28.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand28.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 12) (by change 12 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member29 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand29.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand29.input.fields physical) (List.mem_append_left (a := operand29.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ [])) (List.getElem_mem (l := tuple0_000 physical) (n := 0) (by change 0 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member30 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand30.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand30.input.fields physical) (List.mem_append_left (a := operand30.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ [])) (List.getElem_mem (l := tuple0_000 physical) (n := 1) (by change 1 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member31 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand31.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand31.input.fields physical) (List.mem_append_left (a := operand31.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ [])) (List.getElem_mem (l := tuple0_000 physical) (n := 2) (by change 2 < 16; decide)))


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
