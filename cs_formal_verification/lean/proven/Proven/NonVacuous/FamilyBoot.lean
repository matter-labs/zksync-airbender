module
public import Proven.NonVacuous.PooledBoot
public import Human.Trace.Families.AddSub.RVTheorems

@[expose] public section

/-! The ADD/SUB + word-memory traces (`Data p Family`) of `Human/Trace/Families/AddSub/RVTheorems.lean`: the row and
    boot of `Proven/NonVacuous/PooledBoot.lean` in the two-family registry, booted from the inits/teardowns instance
    (`RVNativeBootBoundary`) or from the registers alone (`RVExecutionBoundary`, no RAM tracked). -/

namespace Airbender.NonVacuous.FamilyBoot
open Trace Arithmetic PooledBoot

def row : Row babyBearModulus := ⟨.addSub, assignment⟩

def program : List RVProgramEntry := [⟨0, 0x002081B3#32, arithmeticFields 1 2 3 0 1⟩]

theorem program_image : rvProgramImageWith rvDecoderFields initial [0] = some program := by kernel_rfl

/-- The row's trace with RAM seeds `rest` after the register seeds. -/
def traceWith (rest : List (MemoryToken babyBearModulus)) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Data babyBearModulus where
  rows := [row]
  rom := rom
  initial := PCState.boundary 0 (4, 0)
  terminal := row.finish
  initialMemory := registerSeeds ++ rest
  terminalMemory := registerTerminal ++ rest

theorem accepted (rest : List (MemoryToken babyBearModulus)) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Accepted (traceWith rest rom) := by
  constructor
  · intro current member
    simp only [traceWith, List.mem_singleton] at member
    subst current
    exact satisfies
  · intro current member
    simp only [traceWith, List.mem_singleton] at member
    subst current
    rfl
  · change [PCState.boundary 0 (4, 0), PooledBoot.row.finish].Perm [PooledBoot.row.finish, PooledBoot.row.start]
    rw [start]
    exact List.Perm.swap _ _ []
  · exact memory_perm rest

theorem decoded (rest : List (MemoryToken babyBearModulus)) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    RVDecoded (traceWith rest rom) program := by
  intro current member
  simp only [traceWith, List.mem_singleton] at member
  subst current
  exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

theorem rows_ne (rest : List (MemoryToken babyBearModulus)) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    (traceWith rest rom).rows ≠ [] := List.cons_ne_nil _ _

/-- Booted from the inits/teardowns instance. -/
noncomputable def bootTrace : Data babyBearModulus :=
  traceWith (inits.flatMap InitsTeardowns.Witness.initTokens) (ROM.table cells (romImageRV initial cells))

theorem boot_boundary : RVNativeBootBoundary bootTrace initial cells program inits where
  distinct := cells_facts.1
  aligned := cells_facts.2
  pc := rfl
  registersZero index := by simp [Cell.readRV, RV.State.getReg, initial]
  topBits := topBits_checked
  seeds := rfl
  domain := rfl
  image := by
    rw [show bootTrace.initialMemory = PooledBoot.trace.initialMemory from rfl]
    exact PooledBoot.image
  initialPC := rfl
  programImage := ⟨[0], program_image⟩
  rom := rfl

/-- Started from the registers alone: no RAM is tracked. -/
noncomputable def registerTrace : Data babyBearModulus :=
  traceWith [] (ROM.table registerCells (romImageRV initial registerCells))

theorem execution_boundary : RVExecutionBoundary registerTrace initial registerCells program where
  distinct := NonVacuous.registerCells_nodup
  aligned cell member := by
    simp only [registerCells, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    trivial
  image := by
    rw [show registerTrace.initialMemory = ROMView.nativeBootImage registerCells by
      simp [registerTrace, traceWith, registerSeeds]]
    exact NonVacuous.initialImageRV_zero fun cell member => by
      simp only [registerCells, List.mem_map] at member
      obtain ⟨_, _, rfl⟩ := member
      simp [Cell.readRV, RV.State.getReg, initial]
  initialPC := ⟨(4, 0), rfl⟩
  programImage := ⟨[0], program_image⟩
  clocks := by
    constructor
    · decide +kernel
    · decide +kernel
    · intro token member
      simp only [registerTrace, traceWith, List.append_nil, registerSeeds, ROMView.nativeBootImage,
        List.mem_map] at member
      obtain ⟨_, _, rfl⟩ := member
      simp only [Cell.initialToken]
      decide +kernel
  rom := rfl

end Airbender.NonVacuous.FamilyBoot
