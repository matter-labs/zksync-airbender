module
public import Proven.NonVacuous.Boot
public import Proven.Constraints
public import Proven.Trace.Timestamps
public import Proven.KernelRfl
public import Human.Helpers.Context.RVPooledBoundary
public import Human.Helpers.Decoder.RVExternalInput
public import Human.Helpers.Decoder.PooledExternalInput
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! A booted six-family pooled trace: the witness that the assumptions of the pooled whole-trace claims can be met
    (`Human/Trace/RVSoundness.lean`, `ZeroTimestamp.lean`, `WritesRangeChecked.lean`, `TeardownBounds.lean`).

    The program is `ADD x3, x1, x2` at PC 0 (ROM bytes `B3 81 20 00`); registers and RAM start at zero. One AddSub row
    executes it at clock four. The RAM is seeded by one instance of the standalone inits/teardowns circuit with top
    bits `0, …, 7` (eight windows of `2 ^ 24` words) and zero teardown columns. The `2 ^ 27` window cells and `Init`
    tokens are never evaluated: their facts come from the inits/teardowns claim. -/

namespace Airbender.NonVacuous.PooledBoot
open Trace Arithmetic List

/-- `ADD x3, x1, x2` at PC 0 and clock 4 on zero registers: the row of `Tests.TraceMemory` with x3 for x2, x2 for x0
    and zero values. Columns: 0-1 PC, 2-3 clock, 4 execute, 5-7 rs1/rs2/rd, 10 the ADD flag, 19-22 the next PC and
    clock, 42-44 the clock-comparison borrows. -/
def assignment (v : Nat) : ZMod babyBearModulus :=
  if v = 2 ∨ v = 19 then 4
  else if v = 21 then 8
  else if v = 4 ∨ v = 5 ∨ v = 10 ∨ v = 42 ∨ v = 43 ∨ v = 44 then 1
  else if v = 6 then 2
  else if v = 7 then 3
  else 0

def row : Row babyBearModulus PooledFamily := ⟨.addSub, assignment⟩

theorem satisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, Arithmetic.limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, Trace.timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | norm_num [babyBearModulus]

/-- The starting state: `ADD x3, x1, x2` (`0x002081B3`) at ROM address 0, zero registers and RAM. -/
def initial : RV.State where
  pc := 0
  regFile _ := 0
  rom a := if a = 0 then 0xB3 else if a = 1 then 0x81 else if a = 2 then 0x20 else 0
  mem _ := 0

/-- The program table entry of the instruction, under either the standard or the CSR 0x7C0-extended metadata. -/
def entry : RVPooledProgramEntry :=
  ⟨0, 0x002081B3#32, (arithmeticFields 1 2 3 0 1).mapFamily pooledArithmeticFamily⟩

def program : List RVPooledProgramEntry := [entry]

theorem program_image : rvProgramImageWith rvPooledDecoderFields initial [0] = some program := by
  kernel_rfl

theorem program_image_extended :
    rvProgramImageWith NonDeterminism.Pooled.rvDecoderFields initial [0] = some program := by
  kernel_rfl

/-- One standalone inits/teardowns instance: top bits `0, …, 7`, zero teardown columns. -/
def init : InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout :=
  ⟨Vector.ofFn fun i => i.val, fun _ _ => 0⟩

def inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout) := [init]

def topBits : List Nat := inits.flatMap fun w => w.topBits.toList

theorem topBits_checked : InitsTeardowns.TopBitsChecked topBits := by
  unfold InitsTeardowns.TopBitsChecked
  decide +kernel

def cells : List Cell := registerCells ++ InitsTeardowns.windowCells InitsTeardowns.importedLayout topBits

/-- The register terminals: x1, x2, x3 as the row wrote them, the other register seeds unchanged. -/
def registerTerminal : List (MemoryToken babyBearModulus) :=
  row.writes ++ (registerSeeds.take 1 ++ registerSeeds.drop 4)

noncomputable def trace : PooledTrace babyBearModulus where
  rows := [row]
  rom := ⟨ROM.table cells (romImageRV initial cells), Verification.subwordTable (ROM.wordsRV initial)⟩
  initial := PCState.boundary 0 (4, 0)
  terminal := row.finish
  initialMemory := registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens
  terminalMemory := registerTerminal ++ inits.flatMap InitsTeardowns.Witness.initTokens

theorem registers_perm : (registerSeeds ++ row.writes).Perm (registerTerminal ++ row.reads) := by
  decide +kernel

/-- The memory matching of the row with any further seeds `rest` (the RAM seeds) passed through unchanged. -/
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

theorem shape : InitsTeardowns.Proofs.Shape InitsTeardowns.importedLayout := ⟨rfl, Or.inr rfl⟩

theorem seeds_image : trace.initialMemory = ROMView.nativeBootImage cells :=
  Proofs.boot_seed_image InitsTeardowns.standalone_claim.1 topBits_checked rfl rfl

theorem cells_facts : cells.Nodup ∧ ∀ cell ∈ cells, cell.Aligned := NonVacuous.boot_cells shape topBits_checked

theorem image : initialImageRV initial cells = some trace.initialMemory := by
  rw [seeds_image]
  exact NonVacuous.initialImageRV_zero fun cell member =>
    NonVacuous.readRV_zero (fun _ => rfl) (fun _ => rfl) cell (cells_facts.2 cell member)

/-- The boot inputs, for either program table (both give the same entry for the instruction). -/
theorem inputs {projection : RV.Instr → Option (DecoderData PooledFamily)}
    (image' : rvProgramImageWith projection initial [0] = some program) :
    RVPooledBootInputs trace initial cells program inits projection where
  registers index := List.mem_append_left _ (NonVacuous.register_mem_registerCells index)
  distinct := cells_facts.1
  aligned := cells_facts.2
  programImage := ⟨[0], image'⟩
  pc := rfl
  registersZero index := by simp [Cell.readRV, RV.State.getReg, initial]
  topBits := topBits_checked
  seeds := rfl
  domain := rfl
  image := image
  initialBoundary := rfl
  wordTable := rfl
  subwordSetup := rfl
  terminalPC := by decide +kernel

theorem decoded : RVPooledDecoded trace program := by
  intro current member
  simp only [trace, List.mem_singleton] at member
  subst current
  exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

theorem ports : NonDeterminism.Pooled.StreamPorts trace initial.input := by
  intro current member read
  simp only [trace, List.mem_singleton] at member
  subst current
  exact absurd read (by decide +kernel)

theorem rows_ne : trace.rows ≠ [] := List.cons_ne_nil _ _

theorem writes_ne : ∃ current ∈ trace.rows, ∃ token, token ∈ current.writes :=
  ⟨row, List.mem_singleton_self _, _, List.mem_cons_self⟩

theorem reads_bounded : ∃ current ∈ trace.rows,
    current.memorySteps ≠ [] ∧ ∀ step ∈ current.memorySteps, step.1.word.Bounded :=
  ⟨row, List.mem_singleton_self _, by decide +kernel⟩

/-- A RAM cell is tracked: the first word of the first window. -/
theorem ram_tracked : ∃ address, Cell.ram address ∈ cells := by
  refine ⟨BitVec.ofNat 32 (InitsTeardowns.windowAddress InitsTeardowns.importedLayout 0 0), List.mem_append_right _ ?_⟩
  simp only [InitsTeardowns.windowCells, List.mem_flatMap, List.mem_map, InitsTeardowns.rows, List.mem_range]
  exact ⟨0, by decide +kernel, 0, Nat.two_pow_pos _, rfl⟩

/-- Every teardown value of the instance is the zero word of its `Init` tuples, and there is a teardown tuple. -/
theorem teardowns : InitsTeardowns.MemoryArgumentReadsBounded inits (trace.rows.flatMap Row.writes) ∧
    ∃ w ∈ inits, ∃ token, token ∈ w.teardownTokens := by
  have first : InitsTeardowns.initToken InitsTeardowns.importedLayout 0 0 ∈
      inits.flatMap (InitsTeardowns.Witness.initTokens (p := babyBearModulus)) := by
    simp only [inits, List.flatMap_cons, List.flatMap_nil, List.append_nil, InitsTeardowns.Witness.initTokens,
      InitsTeardowns.initTokens, List.mem_flatMap, List.mem_map, InitsTeardowns.rows, List.mem_range]
    exact ⟨0, by decide +kernel, 0, Nat.two_pow_pos _, rfl⟩
  refine ⟨fun w hw token htoken => ⟨_, List.mem_append_left _ first, ?_⟩,
    init, List.mem_singleton_self _, _,
    (InitsTeardowns.standalone_claim.1.teardown init).2 0 (by decide +kernel) 0 (Nat.two_pow_pos _) |>.1⟩
  simp only [inits, List.mem_singleton] at hw
  subst hw
  simp only [InitsTeardowns.Witness.teardownTokens, InitsTeardowns.rows, List.mem_flatMap, List.mem_map,
    List.mem_range] at htoken
  obtain ⟨_, _, row, _, rfl⟩ := htoken
  rfl

end Airbender.NonVacuous.PooledBoot
