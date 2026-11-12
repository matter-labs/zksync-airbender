module
public import Proven.Trace.RVRowWitness
public import Proven.ShiftBinop.WitnessCheck
public import Proven.KernelRfl
public import Human.Circuits.ShiftBinop.RVModel
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! The assumptions of the ShiftBinop per-row claim can be met (`Trace.RVRowSatisfiable`): one XOR x1, x2, x0 row
    at PC 0, clock 4, in a one-row pooled trace over all 32 registers (all 0). -/

namespace Airbender.ShiftBinop.Witness
open Arithmetic Trace Trace.Witness Verification

/-- `xor x1, x2, x0`. -/
def bits : BitVec 32 := 0x000140B3

/-- PC 0, all registers 0, the ROM repeating `bits`. -/
def initial : RV.State where
  pc := 0
  regFile := fun _ => 0
  rom := fun x => bits.extractLsb' (8 * (x.toNat % 4)) 8
  mem := fun _ => 0

/-- The row: PC 0 → 4, clock 4 → 8, x2 (0) XOR x0 (0) into x1 (previously 0); all prior accesses at clock 0. The
    byte lookups are those of the XOR test row (tag 4; one tag-3 query). -/
def assignment : Nat → ZMod babyBearModulus
  | 4 | 7 | 12 | 92 | 93 | 94 => 1
  | 5 => 2
  | 55 => 3
  | 2 | 10 | 13 | 64 | 73 | 82 | 91 => 4
  | 15 => 8
  | _ => 0

def row : Row babyBearModulus PooledFamily := ⟨.shiftBinop, assignment⟩

def entry : RVPooledProgramEntry := ⟨0, bits, ⟨.shiftBinop, 2, 0, 1, ⟨0, 0⟩, 2, 4⟩⟩

def trace : PooledTrace babyBearModulus where
  rows := [row]
  rom := ⟨ROM.table registerCells (romImageRV initial registerCells),
    Verification.subwordTable (ROM.wordsRV initial)⟩
  initial := row.start
  terminal := row.finish
  initialMemory := registerSeeds initial
  terminalMemory := row.writes ++ (registerSeeds initial).drop 3

theorem constraints : FlatOperation.ConstraintsHoldFlat (environment assignment) clockConstraints :=
  holds_of_check (by kernel_rfl)

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

theorem assumptions : RVPooledHistoryInputs trace initial registerCells [entry] where
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

def input : RVInput where
  operation := .xor
  immediate := false
  left := 0
  right := 0
  pc := ⟨0, 0⟩
  rs1 := 2
  rs2 := 0
  rd := 1
  encodedImmediate := 0
  before := { initial with pc := row.start.word.toBitVec }

def output : Circuit.Output := ⟨⟨0, 0⟩, ⟨4, 0⟩⟩

theorem words : RVWordMapping input output assignment := by
  constructor <;> decide

theorem satisfiable :
    Trace.RVRowSatisfiable .shiftBinop RVInput.before rvInstruction RVWordMapping RVPooledHistoryInputs :=
  ⟨trace, initial, registerCells, [entry], input, output, assignment, assumptions,
    ⟨accepted, decoded rfl (List.mem_singleton_self _) rfl query, List.mem_singleton_self _⟩,
    ⟨words, row_position rfl initial registerCells, entry, List.mem_singleton_self _, rfl, query, by kernel_rfl⟩⟩

end Airbender.ShiftBinop.Witness
