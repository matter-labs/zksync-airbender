module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member48 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand48.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand48.input.fields physical) (List.mem_append_right (b := operand48.input.fields physical) (bs := (tuple0_001 physical ++ [])) (tuple0_000 physical) (List.mem_append_left (a := operand48.input.fields physical) (as := tuple0_001 physical) ([]) (List.getElem_mem (l := tuple0_001 physical) (n := 3) (by change 3 < 6; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member49 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand49.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand49.input.fields physical) (List.mem_append_right (b := operand49.input.fields physical) (bs := (tuple0_001 physical ++ [])) (tuple0_000 physical) (List.mem_append_left (a := operand49.input.fields physical) (as := tuple0_001 physical) ([]) (List.getElem_mem (l := tuple0_001 physical) (n := 4) (by change 4 < 6; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member50 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand50.input.fields physical = NativeWorkerSetup.rows .columnParity 2 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand50.input.fields physical) (List.mem_append_right (b := operand50.input.fields physical) (bs := (tuple2_001 physical ++ [])) (tuple2_000 physical) (List.mem_append_left (a := operand50.input.fields physical) (as := tuple2_001 physical) ([]) (List.getElem_mem (l := tuple2_001 physical) (n := 13) (by change 13 < 14; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member51 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .columnParity) (selectorsFor .columnParity) physical (NativeWorkerSetup.rows .columnParity)) :
    ∃ index, operand51.input.fields physical = NativeWorkerSetup.rows .columnParity 0 index := by
  kernel_exact native_member (family := .columnParity) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand51.input.fields physical) (List.mem_append_right (b := operand51.input.fields physical) (bs := (tuple0_001 physical ++ [])) (tuple0_000 physical) (List.mem_append_left (a := operand51.input.fields physical) (as := tuple0_001 physical) ([]) (List.getElem_mem (l := tuple0_001 physical) (n := 5) (by change 5 < 6; decide))))


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
