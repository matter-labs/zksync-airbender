module
public import Slop.Trace.RVRowWitness
public import Slop.WitnessCheck
public import Slop.KernelRfl
public import Human.Circuits.AddSub.RVModel
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! The assumptions of the AddSub per-row claim can be met (`Trace.RVRowSatisfiable`): one ADD x1, x2, x0 row at
    PC 0, clock 4, in a one-row pooled trace over all 32 registers (x2 = 18). -/

namespace Airbender.AddSub.Witness
open Arithmetic Reference.RiscV Trace Trace.Witness Verification

/-- `add x1, x2, x0`. -/
def bits : BitVec 32 := 0x000100B3

/-- PC 0, x2 = 18, other registers 0, the ROM repeating `bits`. -/
def initial : RV.State where
  pc := 0
  regFile := fun i => if i = 2 then 18 else 0
  rom := fun x => bits.extractLsb' (8 * (x.toNat % 4)) 8
  mem := fun _ => 0

/-- The row: PC 0 → 4, clock 4 → 8, x2 (18) + x0 (0) into x1 (previously 0); all prior accesses at clock 0. -/
def assignment : Nat → ZMod babyBearModulus
  | 2 | 19 => 4
  | 21 => 8
  | 5 => 2
  | 25 | 33 => 18
  | 4 | 7 | 10 | 42 | 43 | 44 => 1
  | _ => 0

def row : Row babyBearModulus PooledFamily := ⟨.addSub, assignment⟩

def entry : RVPooledProgramEntry := ⟨0, bits, ⟨.addSub, 2, 0, 1, ⟨0, 0⟩, 1, 0⟩⟩

def trace : PooledTrace babyBearModulus where
  rows := [row]
  rom := ⟨ROM.table registerCells (romImageRV initial registerCells),
    Verification.subwordTable (ROM.wordsRV initial)⟩
  initial := row.start
  terminal := row.finish
  initialMemory := registerSeeds initial
  terminalMemory := row.writes ++ (registerSeeds initial).drop 3

theorem constraints : FlatOperation.ConstraintsHoldFlat (environment assignment) clockConstraints :=
  holds_of_checkOps (tables := List.replicate 6 range16Checked ++ List.replicate 8 timestampChecked) rfl
    (by kernel_rfl)

theorem seeds : (registerSeeds (p := babyBearModulus) initial).Perm
    (row.reads ++ (registerSeeds initial).drop 3) := by
  have touched : ((registerSeeds (p := babyBearModulus) initial).take 3).Perm row.reads := by decide
  have whole := touched.append_right ((registerSeeds (p := babyBearModulus) initial).drop 3)
  rwa [List.take_append_drop] at whole

theorem accepted : Accepted trace where
  constraints := by
    intro actual member
    rw [show trace.rows = [row] from rfl, List.mem_singleton] at member
    subst actual
    exact constraints
  active := by
    intro actual member
    rw [show trace.rows = [row] from rfl, List.mem_singleton] at member
    subst actual
    rfl
  states := states_perm row
  memory := by
    simp only [trace, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact memory_perm seeds

theorem entry_image : rvProgramEntryWith rvPooledDecoderFields initial 0 = some entry := by kernel_rfl

theorem query : row.decoderQuery = entry.query := by kernel_rfl

theorem assumptions : RVInterfaceAssumptions trace initial registerCells [entry] where
  initialization :=
    { distinct := registerCells_nodup
      aligned := registerCells_aligned
      image := registerSeeds_image initial
      initialPC := ⟨(4, 0), by kernel_rfl⟩
      programImage := ⟨[0], program_image entry_image⟩
      clocks :=
        { initial := ⟨by decide, by decide⟩
          aligned := by decide
          memory := registerSeeds_bounded initial } }
  wordTable := rfl
  subwordTable := rfl
  registersInitialized := register_mem

def input : RVInput where
  row := ⟨.add, ⟨18, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
  rs1 := 2
  rs2 := 0
  rd := 1
  encodedImmediate := 0
  encodedUpperImmediate := 0
  before := { initial with pc := row.start.word.toBitVec }

def output : Circuit.Output := ⟨⟨18, 0⟩, ⟨4, 0⟩⟩

theorem words : RVWordMapping input output assignment := by
  constructor <;> decide

theorem satisfiable :
    Trace.RVRowSatisfiable .addSub RVInput.before rvInstruction RVWordMapping RVInterfaceAssumptions :=
  ⟨trace, initial, registerCells, [entry], input, output, assignment, assumptions,
    ⟨accepted, decoded rfl (List.mem_singleton_self _) rfl query, List.mem_singleton_self _⟩,
    ⟨words, row_position rfl initial registerCells, entry, List.mem_singleton_self _, rfl, query, by kernel_rfl⟩⟩

end Airbender.AddSub.Witness
