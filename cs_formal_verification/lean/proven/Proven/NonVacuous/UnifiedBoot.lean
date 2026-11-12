module
public import Proven.NonVacuous.Boot
public import Proven.WitnessCheck
public import Proven.Constraints
public import Proven.KernelRfl
public import Human.Helpers.UnifiedReduced.RVExecutionInputs
public import Human.Helpers.UnifiedReduced.Registry
public import Human.Helpers.Core.BabyBearPrime
public import Proven.Trace.RVBootSeed
public import Proven.Final.Circuits.InitsTeardowns.Theorems

@[expose] public section

/-! A booted unified reduced trace: the witness that the assumptions of the unified whole-trace claims can be met
    (`Human/Trace/UnifiedReduced/RVTheorems.lean`, `ZeroTimestamp.lean`, `WritesRangeChecked.lean`,
    `TeardownBounds.lean`).

    The program is `ADD x3, x1, x2` at PC 0 (ROM bytes `B3 81 20 00`); registers and RAM start at zero. One unified
    row executes it at clock four. The RAM is seeded by one instance of the unified machine's inline inits/teardowns
    sets with top bits `0, 1` (two windows of `2 ^ 23` words) and zero teardown columns, never evaluated. -/

namespace Airbender.NonVacuous.UnifiedBoot
open Trace Arithmetic List Verification

/-- `ADD x3, x1, x2` at PC 0 and clock 4 on zero registers. Columns: 0-1 PC, 2-3 clock, 4 execute, 5-7 rs1/rs2/rd,
    11 the ADD selector, 30-33 the next PC and clock, 123-125 the clock-comparison borrows of the three ports. -/
def assignment (v : Nat) : ZMod babyBearModulus :=
  if v = 2 ∨ v = 30 then 4
  else if v = 32 then 8
  else if v = 4 ∨ v = 5 ∨ v = 11 ∨ v = 123 ∨ v = 124 ∨ v = 125 then 1
  else if v = 6 ∨ v = 38 then 2
  else if v = 7 ∨ v = 44 then 3
  else 0

def row : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment⟩

/-- The starting state: `ADD x3, x1, x2` (`0x002081B3`) at ROM address 0, zero registers and RAM. -/
def initial : RV.State where
  pc := 0
  regFile _ := 0
  rom a := if a = 0 then 0xB3 else if a = 1 then 0x81 else if a = 2 then 0x20 else 0
  mem _ := 0

/-- The setup table of `initial`, checked by its index. -/
noncomputable def setupChecked : CheckedTable (ZMod babyBearModulus) :=
  staticChecked (UnifiedReduced.Setup.tableRV initial) rfl

noncomputable def checkedTables : List (CheckedTable (ZMod babyBearModulus)) :=
  List.replicate 13 range16Checked ++ List.replicate 5 setupChecked

theorem lookup_tables :
    (FlatOperation.lookups (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.tableRV (p := babyBearModulus)
      initial))).map Lookup.table = checkedTables.map CheckedTable.table := by
  rfl

theorem timestamp_tables :
    (FlatOperation.lookups (UnifiedReduced.importedConstraintsTimestampLookups (p := babyBearModulus))).map
      Lookup.table = (List.replicate 8 timestampChecked).map CheckedTable.table := by
  rfl

theorem satisfies : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.tableRV initial)) :=
  holds_append (holds_of_checkOps lookup_tables (by kernel_rfl))
    (holds_of_checkOps timestamp_tables (by kernel_rfl))

def program : List UnifiedReduced.RVProgramEntry := [⟨0, 0x002081B3#32, ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 1, 0⟩⟩]

theorem program_image : rvProgramImageWith UnifiedReduced.rvDecoderFields initial [0] = some program := by
  kernel_rfl

/-- One instance of the inline inits/teardowns sets: top bits `0, 1`, zero teardown columns. -/
def init : InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout :=
  ⟨Vector.ofFn fun i => i.val, fun _ _ => 0⟩

def inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout) := [init]

def topBits : List Nat := inits.flatMap fun w => w.topBits.toList

theorem topBits_checked : InitsTeardowns.TopBitsChecked topBits := by
  unfold InitsTeardowns.TopBitsChecked
  decide +kernel

def cells : List Cell := registerCells ++ InitsTeardowns.windowCells InitsTeardowns.unifiedLayout topBits

/-- The register terminals: x1, x2, x3 as the row wrote them, the other register seeds unchanged. -/
def registerTerminal : List (MemoryToken babyBearModulus) :=
  row.writes ++ (registerSeeds.take 1 ++ registerSeeds.drop 4)

noncomputable def trace : UnifiedTrace babyBearModulus where
  rows := [row]
  rom := UnifiedReduced.Setup.tableRV initial
  initial := PCState.boundary 0 (4, 0)
  terminal := row.finish
  initialMemory := registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens
  terminalMemory := registerTerminal ++ inits.flatMap InitsTeardowns.Witness.initTokens

theorem registers_perm : (registerSeeds ++ row.writes).Perm (registerTerminal ++ row.reads) := by
  decide +kernel

theorem memory_perm (rest : List (MemoryToken babyBearModulus)) :
    ((registerSeeds ++ rest) ++ (row.writes ++ [])).Perm ((registerTerminal ++ rest) ++ (row.reads ++ [])) := by
  simp only [List.append_nil, List.append_assoc]
  calc registerSeeds ++ (rest ++ row.writes)
      _ ~ registerSeeds ++ (row.writes ++ rest) := List.perm_append_comm.append_left _
      _ = (registerSeeds ++ row.writes) ++ rest := (List.append_assoc ..).symm
      _ ~ (registerTerminal ++ row.reads) ++ rest := registers_perm.append_right _
      _ = registerTerminal ++ (row.reads ++ rest) := List.append_assoc ..
      _ ~ registerTerminal ++ (rest ++ row.reads) := List.perm_append_comm.append_left _

theorem start : row.start = PCState.boundary 0 (4, 0) := by kernel_rfl

theorem accepted : Accepted trace := by
  constructor
  · intro current member
    simp only [trace, List.mem_singleton] at member
    subst current
    exact satisfies
  · intro current member
    simp only [trace, List.mem_singleton] at member
    subst current
    rfl
  · change [PCState.boundary 0 (4, 0), row.finish].Perm [row.finish, row.start]
    rw [start]
    exact List.Perm.swap _ _ []
  · exact memory_perm _

theorem shape : InitsTeardowns.Proofs.Shape InitsTeardowns.unifiedLayout := ⟨rfl, Or.inl rfl⟩

theorem seeds_image : trace.initialMemory = ROMView.nativeBootImage cells :=
  Proofs.boot_seed_image InitsTeardowns.unified_claim.1 topBits_checked rfl rfl

theorem cells_facts : cells.Nodup ∧ ∀ cell ∈ cells, cell.Aligned := NonVacuous.boot_cells shape topBits_checked

theorem inputs : UnifiedReduced.RVBootInputs trace initial cells program inits where
  distinct := cells_facts.1
  aligned := cells_facts.2
  pc := rfl
  registersZero index := by simp [Cell.readRV, RV.State.getReg, initial]
  topBits := topBits_checked
  seeds := rfl
  domain := rfl
  image := by
    rw [seeds_image]
    exact NonVacuous.initialImageRV_zero fun cell member =>
      NonVacuous.readRV_zero (fun _ => rfl) (fun _ => rfl) cell (cells_facts.2 cell member)
  initialPC := rfl
  programImage := ⟨[0], program_image⟩
  setup := rfl

theorem decoded : UnifiedReduced.RVDecoded trace program := by
  intro current member
  simp only [trace, List.mem_singleton] at member
  subst current
  exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

theorem rows_ne : trace.rows ≠ [] := List.cons_ne_nil _ _

theorem writes_ne : ∃ current ∈ trace.rows, ∃ token, token ∈ current.writes :=
  ⟨row, List.mem_singleton_self _, _, List.mem_cons_self⟩

theorem reads_bounded : ∃ current ∈ trace.rows,
    current.memorySteps ≠ [] ∧ ∀ step ∈ current.memorySteps, step.1.word.Bounded :=
  ⟨row, List.mem_singleton_self _, by decide +kernel⟩

/-- A RAM cell is tracked: the first word of the first window. -/
theorem ram_tracked : ∃ address, Cell.ram address ∈ cells := by
  refine ⟨BitVec.ofNat 32 (InitsTeardowns.windowAddress InitsTeardowns.unifiedLayout 0 0),
    List.mem_append_right _ ?_⟩
  simp only [InitsTeardowns.windowCells, List.mem_flatMap, List.mem_map, InitsTeardowns.rows, List.mem_range]
  exact ⟨0, by decide +kernel, 0, Nat.two_pow_pos _, rfl⟩

/-- Every teardown value of the instance is the zero word of its `Init` tuples, and there is a teardown tuple. -/
theorem teardowns : InitsTeardowns.MemoryArgumentReadsBounded inits (trace.rows.flatMap Row.writes) ∧
    ∃ w ∈ inits, ∃ token, token ∈ w.teardownTokens := by
  have first : InitsTeardowns.initToken InitsTeardowns.unifiedLayout 0 0 ∈
      inits.flatMap (InitsTeardowns.Witness.initTokens (p := babyBearModulus)) := by
    simp only [inits, List.flatMap_cons, List.flatMap_nil, List.append_nil, InitsTeardowns.Witness.initTokens,
      InitsTeardowns.initTokens, List.mem_flatMap, List.mem_map, InitsTeardowns.rows, List.mem_range]
    exact ⟨0, by decide +kernel, 0, Nat.two_pow_pos _, rfl⟩
  refine ⟨fun w hw token htoken => ⟨_, List.mem_append_left _ first, ?_⟩,
    init, List.mem_singleton_self _, _,
    (InitsTeardowns.unified_claim.1.teardown init).2 0 (by decide +kernel) 0 (Nat.two_pow_pos _) |>.1⟩
  simp only [inits, List.mem_singleton] at hw
  subst hw
  simp only [InitsTeardowns.Witness.teardownTokens, InitsTeardowns.rows, List.mem_flatMap, List.mem_map,
    List.mem_range] at htoken
  obtain ⟨_, _, row, _, rfl⟩ := htoken
  rfl

end Airbender.NonVacuous.UnifiedBoot
