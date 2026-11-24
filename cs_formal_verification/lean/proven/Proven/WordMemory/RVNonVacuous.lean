module
public import Human.Circuits.WordMemory.RVTheorems
public import Proven.Constraints
public import Proven.KernelRfl
public import Proven.Trace.RVRowWitness
public import Proven.WitnessCheck

@[expose] public section

/-! The assumptions of the LW/SW claim can be met (`Trace.RVRowSatisfiable`, lean-strategies 3.3): a one-row
    accepted, decoded pooled trace running SW x2,4(x1) at PC 0xFFFC, with x1 = 0x0040FFFC (so the row stores
    x2 = 0x162E04D2 at the RAM word 0x00410000, crossing a limb boundary). The row's constraints are checked by one
    kernel evaluation (`Proven/WitnessCheck.lean`). -/

namespace Airbender.WordMemory.NonVacuous
open Arithmetic Trace Verification

/-- SW x2,4(x1) (`0x0020A223`) at PC 0xFFFC, clock 4: x1/x2 refreshed by the two register ports, RAM written. -/
def assignment : Nat → ZMod babyBearModulus
  | 0 | 17 => 65532
  | 2 | 8 => 4
  | 13 => 8
  | 4 | 5 | 10 | 12 | 33 | 36 | 44 | 46 | 47 | 48 => 1
  | 6 | 19 => 2
  | 18 => 64
  | 23 | 31 => 1234
  | 24 | 32 => 5678
  | 26 => 65
  | 38 => 4259840
  | _ => 0

def initial : RV.State where
  pc := 0xFFFC
  regFile i := if i = 1 then 0x0040FFFC else if i = 2 then 0x162E04D2 else 0
  rom := RV.write (fun _ => 0) 0xFFFC 0x0020A223 4
  mem _ := 0

def cells : List Cell := [.register 1, .register 2, .ram 0x00410000]

def entry : RVPooledProgramEntry := ⟨0xFFFC, 0x0020A223, ⟨.wordMemory, 1, 2, 0, Word.ofBitVec 4, 1, 0⟩⟩

def row : Row babyBearModulus PooledFamily := ⟨.wordMemory, assignment⟩

def token (cell : Cell) (time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨cell.addressCode, (time, 0), Nat.pair lo hi⟩

def trace : PooledTrace babyBearModulus where
  rows := [row]
  rom := ⟨ROM.table cells (romImageRV initial cells), subwordTable (ROM.wordsRV initial)⟩
  initial := row.start
  terminal := row.finish
  initialMemory := [token (.register 1) 0 65532 64, token (.register 2) 0 1234 5678, token (.ram 0x00410000) 0 0 0]
  terminalMemory :=
    [token (.register 1) 4 65532 64, token (.register 2) 5 1234 5678, token (.ram 0x00410000) 6 1234 5678]

def input : RVInput where
  store := true
  source := ⟨65532, 64⟩
  immediate := ⟨4, 0⟩
  readData := ⟨1234, 5678⟩
  pc := ⟨65532, 0⟩
  rs1 := 1
  rs2 := 2
  rd := 0
  encodedImmediate := 4
  before := { initial with pc := row.start.word.toBitVec }

def output : Output := ⟨⟨0, 65⟩, ⟨1234, 5678⟩, ⟨0, 1⟩⟩

theorem constraints : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (clockConstraints (ROM.table cells (romImageRV initial cells))) := by
  apply holds_append
  · exact holds_of_checkOps (tables := List.replicate 3 range16Checked ++
      [staticChecked (ROM.table cells (romImageRV (p := babyBearModulus) initial cells)) rfl]) rfl (by kernel_rfl)
  · exact holds_of_checkOps (tables := List.replicate 8 timestampChecked) rfl (by kernel_rfl)

theorem accepted : Accepted trace where
  constraints actual member := by
    rw [show trace.rows = [row] from rfl, List.mem_singleton] at member
    subst member
    exact constraints
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

theorem inputs : RVPooledHistoryInputs trace initial cells [entry] where
  initialization := {
    distinct := by decide
    aligned := by
      intro cell member
      simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl <;> trivial
    image := by kernel_rfl
    initialPC := ⟨(4, 0), by kernel_rfl⟩
    programImage := ⟨[0xFFFC], by kernel_rfl⟩
    clocks := boundary }
  wordTable := rfl
  subwordTable := rfl

theorem query : row.decoderQuery = entry.query := by kernel_rfl

theorem satisfiable : Trace.RVRowSatisfiable .wordMemory RVInput.before rvInstruction RVWordMapping
    Trace.RVPooledHistoryInputs :=
  ⟨trace, initial, cells, [entry], input, output, assignment, inputs,
    ⟨accepted, Witness.decoded rfl (List.mem_singleton_self _) rfl query, List.mem_singleton_self _⟩,
    { words := by constructor <;> kernel_rfl
      state := Witness.row_position rfl initial cells
      instruction := ⟨entry, List.mem_singleton_self _, rfl, query, by kernel_rfl⟩ }⟩

end Airbender.WordMemory.NonVacuous
