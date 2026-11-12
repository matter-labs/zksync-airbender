module
public import Human.Circuits.JumpBranchSlt.RVTheorems
public import Slop.JumpBranchSlt.WitnessCheck
public import Slop.KernelRfl
public import Slop.Trace.RVRowWitness

@[expose] public section

/-! The assumptions of the comparison, branch and jump claims can be met (`Trace.RVRowSatisfiable`,
    lean-strategies 3.3): for each, a one-row accepted, decoded pooled trace at PC 0, clock 4, with the row's final PC
    as the (canonical) terminal PC. The rows' constraints are checked by one kernel evaluation each
    (`Slop/WitnessCheck.lean`). -/

namespace Airbender.JumpBranchSlt.NonVacuous
open Trace

/-- A seed or final register token: register `index` at clock `time` holding the word `⟨lo, hi⟩`. -/
def token (index : BitVec 5) (time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register index).addressCode, (time, 0), Nat.pair lo hi⟩

end Airbender.JumpBranchSlt.NonVacuous

namespace Airbender.JumpBranchSlt.Comparison.NonVacuous
open Arithmetic Trace Verification JumpBranchSlt.NonVacuous

/-- SLTU x2,x1,x2 (`0x0020B133`) with x1 = 0 and x2 = 0xFFFFFFFF: x2 := 1. -/
def assignment : Nat → ZMod babyBearModulus
  | 2 => 4
  | 18 => 8
  | 4 | 5 | 13 | 30 | 34 | 37 | 38 | 44 | 47 | 49 | 50 | 51 => 1
  | 6 | 7 => 2
  | 10 => 3
  | 16 | 36 => 4
  | 26 | 27 | 28 | 29 | 43 => 65535
  | 32 => 5
  | _ => 0

def initial : RV.State where
  pc := 0
  regFile i := if i = 2 then 0xFFFFFFFF else 0
  rom := RV.write (fun _ => 0) 0 0x0020B133 4
  mem _ := 0

def cells : List Cell := [.register 1, .register 2]

def entry : RVPooledProgramEntry := ⟨0, 0x0020B133, ⟨.jumpBranchSlt, 1, 2, 2, Word.ofBitVec 0, 4, 3⟩⟩

def row : Row babyBearModulus PooledFamily := ⟨.jumpBranchSlt, assignment⟩

def trace : PooledTrace babyBearModulus where
  rows := [row]
  rom := ⟨ROM.table cells (romImageRV initial cells), subwordTable (ROM.wordsRV initial)⟩
  initial := row.start
  terminal := row.finish
  initialMemory := [token 1 0 0 0, token 2 0 65535 65535]
  terminalMemory := [token 1 4 0 0, token 2 6 1 0]

def input : RVInput where
  opcode := .sltu
  left := ⟨0, 0⟩
  right := ⟨65535, 65535⟩
  pc := ⟨0, 0⟩
  rs1 := 1
  rs2 := 2
  rd := 2
  encodedImmediate := 0
  before := { initial with pc := row.start.word.toBitVec }

def output : Circuit.Output := ⟨⟨1, 0⟩, ⟨4, 0⟩⟩

theorem accepted : Accepted trace where
  constraints actual member := by
    rw [show trace.rows = [row] from rfl, List.mem_singleton] at member
    subst member
    exact holds_of_check (by kernel_rfl) (by kernel_rfl)
  active actual member := by
    rw [show trace.rows = [row] from rfl, List.mem_singleton] at member
    subst member
    rfl
  states := List.Perm.swap _ _ []
  memory := by
    dsimp only [trace]
    decide

theorem boundary : ClockBoundary trace where
  initial := by
    change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  aligned := by
    change 4 % 4 = 0
    decide
  memory token member := by
    simp only [trace, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

theorem inputs : RVTraceInputs trace initial cells [entry] where
  initialization := {
    distinct := by decide
    aligned := by
      intro cell member
      simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl <;> trivial
    image := by kernel_rfl
    initialPC := ⟨(4, 0), by kernel_rfl⟩
    programImage := ⟨[0], by kernel_rfl⟩
    clocks := boundary }
  wordTable := rfl
  subwordTable := rfl
  terminalPC := by constructor <;> decide

theorem query : row.decoderQuery = entry.query := by kernel_rfl

theorem satisfiable : Trace.RVRowSatisfiable .jumpBranchSlt RVInput.before rvInstruction RVWordMapping
    RVTraceInputs :=
  ⟨trace, initial, cells, [entry], input, output, assignment, inputs,
    ⟨accepted, Witness.decoded rfl (List.mem_singleton_self _) rfl query, List.mem_singleton_self _⟩,
    { words := by constructor <;> kernel_rfl
      state := Witness.row_position rfl initial cells
      instruction := ⟨entry, List.mem_singleton_self _, rfl, query, by kernel_rfl⟩ }⟩

end Airbender.JumpBranchSlt.Comparison.NonVacuous

namespace Airbender.JumpBranchSlt.Branch.NonVacuous
open Arithmetic Trace Verification JumpBranchSlt.NonVacuous

/-- BEQ x1,x2,-4 (`0xFE208EE3`) with x1 = 0 and x2 = 0xFFFFFFFF: not taken, PC := 4. -/
def assignment : Nat → ZMod babyBearModulus
  | 2 => 4
  | 18 => 8
  | 4 | 5 | 14 | 15 | 34 | 37 | 38 | 49 | 50 | 51 => 1
  | 6 => 2
  | 8 => 65532
  | 9 => 65535
  | 16 | 36 => 4
  | 26 | 27 | 43 => 65535
  | _ => 0

def initial : RV.State where
  pc := 0
  regFile i := if i = 2 then 0xFFFFFFFF else 0
  rom := RV.write (fun _ => 0) 0 0xFE208EE3 4
  mem _ := 0

def cells : List Cell := [.register 0, .register 1, .register 2]

def entry : RVPooledProgramEntry := ⟨0, 0xFE208EE3, ⟨.jumpBranchSlt, 1, 2, 0, ⟨65532, 65535⟩, 24, 0⟩⟩

def row : Row babyBearModulus PooledFamily := ⟨.jumpBranchSlt, assignment⟩

def trace : PooledTrace babyBearModulus where
  rows := [row]
  rom := ⟨ROM.table cells (romImageRV initial cells), subwordTable (ROM.wordsRV initial)⟩
  initial := row.start
  terminal := row.finish
  initialMemory := [token 0 0 0 0, token 1 0 0 0, token 2 0 65535 65535]
  terminalMemory := [token 0 6 0 0, token 1 4 0 0, token 2 5 65535 65535]

def input : RVInput where
  cond := .eq
  left := ⟨0, 0⟩
  right := ⟨65535, 65535⟩
  offset := ⟨65532, 65535⟩
  pc := ⟨0, 0⟩
  rs1 := 1
  rs2 := 2
  encodedOffset := 0x1FFC
  before := { initial with pc := row.start.word.toBitVec }

def output : Circuit.Output := ⟨⟨0, 0⟩, ⟨4, 0⟩⟩

theorem accepted : Accepted trace where
  constraints actual member := by
    rw [show trace.rows = [row] from rfl, List.mem_singleton] at member
    subst member
    exact holds_of_check (by kernel_rfl) (by kernel_rfl)
  active actual member := by
    rw [show trace.rows = [row] from rfl, List.mem_singleton] at member
    subst member
    rfl
  states := List.Perm.swap _ _ []
  memory := by
    dsimp only [trace]
    decide

theorem boundary : ClockBoundary trace where
  initial := by
    change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  aligned := by
    change 4 % 4 = 0
    decide
  memory token member := by
    simp only [trace, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

theorem inputs : RVTraceInputs trace initial cells [entry] where
  initialization := {
    distinct := by decide
    aligned := by
      intro cell member
      simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl <;> trivial
    image := by kernel_rfl
    initialPC := ⟨(4, 0), by kernel_rfl⟩
    programImage := ⟨[0], by kernel_rfl⟩
    clocks := boundary }
  wordTable := rfl
  subwordTable := rfl
  terminalPC := by constructor <;> decide

theorem query : row.decoderQuery = entry.query := by kernel_rfl

theorem satisfiable : Trace.RVRowSatisfiable .jumpBranchSlt RVInput.before rvInstruction RVWordMapping
    RVTraceInputs :=
  ⟨trace, initial, cells, [entry], input, output, assignment, inputs,
    ⟨accepted, Witness.decoded rfl (List.mem_singleton_self _) rfl query, List.mem_singleton_self _⟩,
    { words := by constructor <;> kernel_rfl
      state := Witness.row_position rfl initial cells
      instruction := ⟨entry, List.mem_singleton_self _, rfl, query, by kernel_rfl⟩ }⟩

end Airbender.JumpBranchSlt.Branch.NonVacuous

namespace Airbender.JumpBranchSlt.Jump.NonVacuous
open Arithmetic Trace Verification JumpBranchSlt.NonVacuous

/-- JALR x1,-4(x1) (`0xFFC080E7`) with x1 = 5: PC := (5 - 4) with bit 0 cleared = 0, x1 := 4. -/
def assignment : Nat → ZMod babyBearModulus
  | 2 => 4
  | 18 => 8
  | 4 | 5 | 7 | 12 | 36 | 39 | 40 | 49 | 50 | 51 => 1
  | 8 => 65532
  | 9 => 65535
  | 22 | 28 => 5
  | 30 | 32 | 34 | 47 => 4
  | _ => 0

def initial : RV.State where
  pc := 0
  regFile i := if i = 1 then 5 else 0
  rom := RV.write (fun _ => 0) 0 0xFFC080E7 4
  mem _ := 0

def cells : List Cell := [.register 0, .register 1]

def entry : RVPooledProgramEntry := ⟨0, 0xFFC080E7, ⟨.jumpBranchSlt, 1, 0, 1, ⟨65532, 65535⟩, 2, 0⟩⟩

def row : Row babyBearModulus PooledFamily := ⟨.jumpBranchSlt, assignment⟩

def trace : PooledTrace babyBearModulus where
  rows := [row]
  rom := ⟨ROM.table cells (romImageRV initial cells), subwordTable (ROM.wordsRV initial)⟩
  initial := row.start
  terminal := row.finish
  initialMemory := [token 0 0 0 0, token 1 0 5 0]
  terminalMemory := [token 0 5 0 0, token 1 6 4 0]

def input : RVInput where
  instruction := .jalr 0xFFC
  source := ⟨5, 0⟩
  offset := ⟨65532, 65535⟩
  pc := ⟨0, 0⟩
  rs1 := 1
  rd := 1
  before := { initial with pc := row.start.word.toBitVec }

def output : Circuit.Output := ⟨⟨4, 0⟩, ⟨0, 0⟩⟩

theorem accepted : Accepted trace where
  constraints actual member := by
    rw [show trace.rows = [row] from rfl, List.mem_singleton] at member
    subst member
    exact holds_of_check (by kernel_rfl) (by kernel_rfl)
  active actual member := by
    rw [show trace.rows = [row] from rfl, List.mem_singleton] at member
    subst member
    rfl
  states := List.Perm.swap _ _ []
  memory := by
    dsimp only [trace]
    decide

theorem boundary : ClockBoundary trace where
  initial := by
    change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  aligned := by
    change 4 % 4 = 0
    decide
  memory token member := by
    simp only [trace, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

theorem inputs : RVTraceInputs trace initial cells [entry] where
  initialization := {
    distinct := by decide
    aligned := by
      intro cell member
      simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl <;> trivial
    image := by kernel_rfl
    initialPC := ⟨(4, 0), by kernel_rfl⟩
    programImage := ⟨[0], by kernel_rfl⟩
    clocks := boundary }
  wordTable := rfl
  subwordTable := rfl
  terminalPC := by constructor <;> decide

theorem query : row.decoderQuery = entry.query := by kernel_rfl

theorem satisfiable : Trace.RVRowSatisfiable .jumpBranchSlt RVInput.before rvInstruction RVWordMapping
    RVTraceInputs :=
  ⟨trace, initial, cells, [entry], input, output, assignment, inputs,
    ⟨accepted, Witness.decoded rfl (List.mem_singleton_self _) rfl query, List.mem_singleton_self _⟩,
    { words := by constructor <;> first | kernel_rfl | (intro _; kernel_rfl)
      state := Witness.row_position rfl initial cells
      instruction := ⟨entry, List.mem_singleton_self _, rfl, query, by kernel_rfl⟩ }⟩

end Airbender.JumpBranchSlt.Jump.NonVacuous
