module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member16 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .chi5) (selectorsFor .chi5) physical (NativeWorkerSetup.rows .chi5)) :
    ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  kernel_exact native_member (family := .chi5) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand16.input.fields physical) (List.mem_append_left (a := operand16.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ [])) (List.getElem_mem (l := tuple0_000 physical) (n := 15) (by change 15 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member17 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .chi5) (selectorsFor .chi5) physical (NativeWorkerSetup.rows .chi5)) :
    ∃ index, operand17.input.fields physical = NativeWorkerSetup.rows .chi5 0 index := by
  kernel_exact native_member (family := .chi5) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand17.input.fields physical) (List.mem_append_right (b := operand17.input.fields physical) (bs := (tuple0_001 physical ++ [])) (tuple0_000 physical) (List.mem_append_left (a := operand17.input.fields physical) (as := tuple0_001 physical) ([]) (List.getElem_mem (l := tuple0_001 physical) (n := 0) (by change 0 < 1; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member18 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .chi5) (selectorsFor .chi5) physical (NativeWorkerSetup.rows .chi5)) :
    ∃ index, operand18.input.fields physical = NativeWorkerSetup.rows .chi5 2 index := by
  kernel_exact native_member (family := .chi5) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 2) (values := operand18.input.fields physical) (List.mem_append_left (a := operand18.input.fields physical) (as := tuple2_000 physical) ([]) (List.getElem_mem (l := tuple2_000 physical) (n := 1) (by change 1 < 2; decide)))


end Airbender.Compiler.WorkerConstraints.KeccakChi5
