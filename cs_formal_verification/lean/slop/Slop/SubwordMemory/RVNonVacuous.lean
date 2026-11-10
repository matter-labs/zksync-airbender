module
public import Human.Circuits.SubwordMemory.RVTheorems
public import Slop.Constraints
public import Slop.KernelRfl
public import Slop.SubwordMemory.WitnessCheck
public import Slop.Trace.RVSingleRow

@[expose] public section

/-! The assumptions of the subword claim can be met (`Trace.RVRowSatisfiable`, lean-strategies 3.3): a one-row
    accepted, decoded pooled trace running LBU x2,0(x1) at PC 0, with x1 = 0x00400001 and the RAM word 0x56781234
    at 0x00400000 (so x2 := 0x12). The row's constraints are checked by one kernel evaluation
    (`Slop/WitnessCheck.lean`). -/

namespace Airbender.SubwordMemory.NonVacuous
open Arithmetic Trace Verification

/-- LBU x2,0(x1) (`0x0000C103`) at PC 0, clock 4: x1 read, the RAM word read, x2 written. -/
def assignment : Nat → ZMod babyBearModulus
  | 2 | 13 => 4
  | 15 => 8
  | 4 | 5 | 11 | 19 | 35 | 47 | 60 | 62 | 63 | 64 => 1
  | 7 | 27 => 2
  | 20 | 22 => 64
  | 25 => 4660
  | 26 => 22136
  | 33 | 53 | 54 | 55 => 18
  | 44 => 65536
  | 49 => 20971520
  | 50 | 52 => 135732
  | 51 => 70196
  | 59 | 61 => 43
  | _ => 0

def initial : RV.State where
  pc := 0
  regFile i := if i = 1 then 0x00400001 else 0
  rom := RV.write (fun _ => 0) 0 0x0000C103 4
  mem := RV.write (fun _ => 0) 0x00400000 0x56781234 4

def cells : List Cell := [.register 1, .register 2, .ram 0x00400000]

def entry : RVPooledProgramEntry := ⟨0, 0x0000C103, ⟨.subwordMemory, 1, 0, 2, Word.ofBitVec 0, 2, 0⟩⟩

def row : Row babyBearModulus PooledFamily := ⟨.subwordMemory, assignment⟩

def token (cell : Cell) (time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨cell.addressCode, (time, 0), Nat.pair lo hi⟩

def trace : PooledTrace babyBearModulus where
  rows := [row]
  rom := ⟨ROM.table cells (romImageRV initial cells), subwordTable (ROM.wordsRV initial)⟩
  initial := row.start
  terminal := row.finish
  initialMemory := [token (.register 1) 0 1 64, token (.register 2) 0 0 0, token (.ram 0x00400000) 0 4660 22136]
  terminalMemory := [token (.register 1) 4 1 64, token (.register 2) 6 18 0, token (.ram 0x00400000) 5 4660 22136]

def input : RVInput where
  store := false
  byte := true
  signed := false
  source := ⟨1, 64⟩
  immediate := ⟨0, 0⟩
  readData := ⟨4660, 22136⟩
  oldData := ⟨0, 0⟩
  pc := ⟨0, 0⟩
  rs1 := 1
  rs2 := 0
  rd := 2
  encodedImmediate := 0
  before := { initial with pc := row.start.word.toBitVec }

def output : Output := ⟨⟨0, 64⟩, ⟨18, 0⟩, ⟨4, 0⟩⟩

theorem constraints : FlatOperation.ConstraintsHoldFlat (environment assignment)
    (clockConstraints (subwordTable (ROM.wordsRV initial))) := by
  apply holds_append
  · exact holds_of_check (subwordChecked _) rfl (by kernel_rfl)
  · exact timestamps_of_check (by kernel_rfl)

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
    programImage := ⟨[0], by kernel_rfl⟩
    clocks := boundary }
  wordTable := rfl
  subwordTable := rfl

theorem query : row.decoderQuery = entry.query := by kernel_rfl

theorem satisfiable : Trace.RVRowSatisfiable .subwordMemory RVInput.before rvInstruction RVWordMapping
    Trace.RVPooledHistoryInputs :=
  ⟨trace, initial, cells, [entry], input, output, assignment, inputs,
    ⟨accepted, Proofs.rv_pooled_decoded_single rfl rfl query, List.mem_singleton_self _⟩,
    { words := by constructor <;> first | kernel_rfl | (intro h; exact absurd h Bool.false_ne_true)
      state := Proofs.rv_row_position_single rfl initial cells
      instruction := ⟨entry, List.mem_singleton_self _, rfl, query, by kernel_rfl⟩ }⟩

end Airbender.SubwordMemory.NonVacuous
