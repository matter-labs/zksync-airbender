module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Tuples
public import Proven.KernelExact

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member32 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand32.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand32.input.fields physical) (List.mem_append_right (b := operand32.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_left (a := operand32.input.fields physical) (as := tuple0_001 physical) ((tuple0_002 physical ++ (tuple0_003 physical ++ []))) (List.getElem_mem (l := tuple0_001 physical) (n := 15) (by change 15 < 16; decide))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member33 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand33.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand33.input.fields physical) (List.mem_append_right (b := operand33.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand33.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand33.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 0) (by change 0 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member34 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand34.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand34.input.fields physical) (List.mem_append_right (b := operand34.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand34.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand34.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 1) (by change 1 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member35 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand35.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand35.input.fields physical) (List.mem_append_right (b := operand35.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand35.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand35.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 2) (by change 2 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member36 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand36.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand36.input.fields physical) (List.mem_append_right (b := operand36.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand36.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand36.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 3) (by change 3 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member37 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand37.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand37.input.fields physical) (List.mem_append_right (b := operand37.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand37.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand37.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 4) (by change 4 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member38 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand38.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand38.input.fields physical) (List.mem_append_right (b := operand38.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand38.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand38.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 5) (by change 5 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member39 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand39.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand39.input.fields physical) (List.mem_append_right (b := operand39.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand39.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand39.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 6) (by change 6 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member40 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand40.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand40.input.fields physical) (List.mem_append_right (b := operand40.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand40.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand40.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 7) (by change 7 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member41 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand41.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand41.input.fields physical) (List.mem_append_right (b := operand41.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand41.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand41.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 8) (by change 8 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member42 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand42.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand42.input.fields physical) (List.mem_append_right (b := operand42.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand42.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand42.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 9) (by change 9 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member43 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand43.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand43.input.fields physical) (List.mem_append_right (b := operand43.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand43.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand43.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 10) (by change 10 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member44 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand44.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand44.input.fields physical) (List.mem_append_right (b := operand44.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand44.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand44.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 11) (by change 11 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member45 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand45.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand45.input.fields physical) (List.mem_append_right (b := operand45.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand45.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand45.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 12) (by change 12 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member46 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand46.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand46.input.fields physical) (List.mem_append_right (b := operand46.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand46.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand46.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 13) (by change 13 < 16; decide)))))

/-- Exact native matching supplies the public row for this primitive tuple. -/
theorem member47 (physical : GKRAddress → F)
    (arguments : NativeLookups.Arguments (circuitFor .thetaRho) (selectorsFor .thetaRho) physical (NativeWorkerSetup.rows .thetaRho)) :
    ∃ index, operand47.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  kernel_exact native_member (family := .thetaRho) (physical := physical) (tuples := tuples physical) arguments (binding physical) (group := 0) (values := operand47.input.fields physical) (List.mem_append_right (b := operand47.input.fields physical) (bs := (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ [])))) (tuple0_000 physical) (List.mem_append_right (b := operand47.input.fields physical) (bs := (tuple0_002 physical ++ (tuple0_003 physical ++ []))) (tuple0_001 physical) (List.mem_append_left (a := operand47.input.fields physical) (as := tuple0_002 physical) ((tuple0_003 physical ++ [])) (List.getElem_mem (l := tuple0_002 physical) (n := 14) (by change 14 < 16; decide)))))


end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
