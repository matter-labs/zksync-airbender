module
public import Slop.Trace.RVRowWitness
public import Slop.MulDiv.WitnessCheck
public import Slop.KernelRfl
public import Human.Circuits.MulDiv.RVModel
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

/-! The assumptions of the MulDiv per-row claim can be met (`Trace.RVRowSatisfiable`): one DIVU x1, x2, x0 row
    (division by zero: all ones) at PC 0, clock 4, in a one-row pooled trace over all 32 registers (x2 = 0x20007). -/

namespace Airbender.MulDiv.Witness
open Arithmetic Trace Trace.Witness Verification

/-- `divu x1, x2, x0`. -/
def bits : BitVec 32 := 0x020150B3

/-- PC 0, x2 = 0x20007, other registers 0, the ROM repeating `bits`. -/
def initial : RV.State where
  pc := 0
  regFile := fun i => if i = 2 then 0x20007 else 0
  rom := fun x => bits.extractLsb' (8 * (x.toNat % 4)) 8
  mem := fun _ => 0

/-- The row: PC 0 → 4, clock 4 → 8, x2 (0x20007) divided by x0 (0) into x1 (previously 0), quotient all ones;
    all prior accesses at clock 0. The auxiliary columns are those of the division-by-zero test row. -/
def assignment : Nat → ZMod babyBearModulus
  | 4 | 7 | 12 | 32 | 44 | 55 | 65 | 66 | 67 => 1
  | 5 => 2
  | 2 | 14 => 4
  | 16 => 8
  | 20 | 37 | 39 | 45 | 51 | 56 => 7
  | 21 | 38 | 40 | 46 | 52 | 57 => 2
  | 28 | 29 | 49 | 50 => 65535
  | 35 | 36 | 60 | 61 => 255
  | _ => 0

def row : Row babyBearModulus PooledFamily := ⟨.mulDiv, assignment⟩

def entry : RVPooledProgramEntry := ⟨0, bits, ⟨.mulDiv, 2, 0, 1, ⟨0, 0⟩, 4, 0⟩⟩

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
  operation := .divu
  left := ⟨7, 2⟩
  right := ⟨0, 0⟩
  pc := ⟨0, 0⟩
  rs1 := 2
  rs2 := 0
  rd := 1
  before := { initial with pc := row.start.word.toBitVec }

def output : Circuit.Output := ⟨⟨65535, 65535⟩, ⟨4, 0⟩⟩

theorem words : RVWordMapping input output assignment := by
  constructor <;> decide

theorem satisfiable :
    Trace.RVRowSatisfiable .mulDiv RVInput.before rvInstruction RVWordMapping RVPooledHistoryInputs :=
  ⟨trace, initial, registerCells, [entry], input, output, assignment, assumptions,
    ⟨accepted, decoded rfl (List.mem_singleton_self _) rfl query, List.mem_singleton_self _⟩,
    ⟨words, row_position rfl initial registerCells, entry, List.mem_singleton_self _, rfl, query, by kernel_rfl⟩⟩

end Airbender.MulDiv.Witness
