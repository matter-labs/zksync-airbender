module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member96 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand96.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand96.input.fields physical) (List.mem_append_left (a := operand96.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (List.getElem_mem (l := tuple0_000 physical) (n := 7) (by change 7 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member97 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand97.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand97.input.fields physical) (List.mem_append_left (a := operand97.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (List.getElem_mem (l := tuple0_000 physical) (n := 8) (by change 8 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member98 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand98.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand98.input.fields physical) (List.mem_append_left (a := operand98.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (List.getElem_mem (l := tuple0_000 physical) (n := 9) (by change 9 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member99 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand99.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand99.input.fields physical) (List.mem_append_left (a := operand99.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (List.getElem_mem (l := tuple0_000 physical) (n := 10) (by change 10 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member100 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand100.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand100.input.fields physical) (List.mem_append_left (a := operand100.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (List.getElem_mem (l := tuple0_000 physical) (n := 11) (by change 11 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member101 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand101.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand101.input.fields physical) (List.mem_append_left (a := operand101.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (List.getElem_mem (l := tuple0_000 physical) (n := 12) (by change 12 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member102 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand102.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand102.input.fields physical) (List.mem_append_left (a := operand102.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (List.getElem_mem (l := tuple0_000 physical) (n := 13) (by change 13 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member103 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand103.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand103.input.fields physical) (List.mem_append_left (a := operand103.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (List.getElem_mem (l := tuple0_000 physical) (n := 14) (by change 14 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member104 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand104.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand104.input.fields physical) (List.mem_append_left (a := operand104.input.fields physical) (as := tuple0_000 physical) ((tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (List.getElem_mem (l := tuple0_000 physical) (n := 15) (by change 15 < 16; decide)))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member105 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand105.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand105.input.fields physical) (List.mem_append_right (b := operand105.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (tuple0_000 physical) (List.mem_append_left (a := operand105.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))))))) (List.getElem_mem (l := tuple0_001 physical) (n := 0) (by change 0 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member106 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand106.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand106.input.fields physical) (List.mem_append_right (b := operand106.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (tuple0_000 physical) (List.mem_append_left (a := operand106.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))))))) (List.getElem_mem (l := tuple0_001 physical) (n := 1) (by change 1 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member107 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand107.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand107.input.fields physical) (List.mem_append_right (b := operand107.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (tuple0_000 physical) (List.mem_append_left (a := operand107.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))))))) (List.getElem_mem (l := tuple0_001 physical) (n := 2) (by change 2 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member108 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand108.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand108.input.fields physical) (List.mem_append_right (b := operand108.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (tuple0_000 physical) (List.mem_append_left (a := operand108.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))))))) (List.getElem_mem (l := tuple0_001 physical) (n := 3) (by change 3 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member109 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand109.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand109.input.fields physical) (List.mem_append_right (b := operand109.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (tuple0_000 physical) (List.mem_append_left (a := operand109.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))))))) (List.getElem_mem (l := tuple0_001 physical) (n := 4) (by change 4 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member110 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand110.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand110.input.fields physical) (List.mem_append_right (b := operand110.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (tuple0_000 physical) (List.mem_append_left (a := operand110.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))))))) (List.getElem_mem (l := tuple0_001 physical) (n := 5) (by change 5 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member111 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .blakeRound) (selectorsFor .blakeRound) physical (NativeWorkerSetup.rows .blakeRound)) :
    ∃ index, operand111.input.fields physical = NativeWorkerSetup.rows .blakeRound 0 index := by
  kernel_exact native_member (family := .blakeRound) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand111.input.fields physical) (List.mem_append_right (b := operand111.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))) (tuple0_000 physical) (List.mem_append_left (a := operand111.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ []))))))))))) (List.getElem_mem (l := tuple0_001 physical) (n := 6) (by change 6 < 16; decide))))


end Airbender.Compiler.WorkerConstraints.BlakeRound
