import Tests.SubwordMemoryTimestamp
import Airbender.Proofs.SubwordMemory.Values
import Airbender.Proofs.Sail.WordMemoryState

namespace Tests.SubwordMemoryHistory
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private def entry : Airbender.SubwordMemory.ProgramEntry :=
  ⟨0, 0x0000c103, .LOAD (0, .Regidx 1, .Regidx 2, true, 1),
    ⟨(), 1, 0, 2, ⟨0, 0⟩, 2, 0⟩⟩
private def initial : State := { (default : State) with regs :=
  (((default : State).regs.insert .x1 (0x00400001 : BitVec 32)).insert .x2 (0 : BitVec 32)).insert .PC 0 }
private def dataState := wordWriteState initial 4194304 0x56781234
private def before := wordWriteState dataState 0 entry.bits
private def cells : List Cell := [.register 1, .ram 4194304, .register 2]
private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 1) 0x00400001,
    Cell.initialToken (.ram 4194304) 0x56781234, Cell.initialToken (.register 2) 0]
private def row : Row babyBearModulus Airbender.SubwordMemory.TraceKind :=
  ⟨.subwordMemory, Tests.SubwordMemoryTimestamp.assignment false⟩
private def trace : Airbender.SubwordMemory.NativeTrace babyBearModulus where
  rows := [row]
  rom := Verification.subwordTable (fun _ => 0)
  initial := row.start
  terminal := row.finish
  initialMemory := seed
  terminalMemory := [⟨(Cell.register 1).addressCode, (4, 0), Nat.pair 1 64⟩,
    ⟨(Cell.ram 4194304).addressCode, (5, 0), Nat.pair 4660 22136⟩,
    ⟨(Cell.register 2).addressCode, (6, 0), Nat.pair 18 0⟩]

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact Tests.SubwordMemoryTimestamp.constraints false
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, row,
      Airbender.SubwordMemory.importedConstraintsMemoryPorts,
      Airbender.SubwordMemory.importedConstraintsTraceColumns]
    decide

private theorem boundary : ClockBoundary trace := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

private theorem image : initialImage before cells = some seed := by
  have one : (Cell.register 1).read before = .ok 0x00400001 before := by
    apply read_register
    simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read before = .ok 0 before := by
    apply read_register
    simp [before, dataState, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  have memory : (Cell.ram 4194304).read before = .ok 0x56781234 before :=
    written_word_disjoint 0 entry.bits (Or.inr (by decide)) (written_word_read initial 4194304 0x56781234)
  simp only [initialImage, cells, seed, List.mapM_cons, List.mapM_nil, one, two, memory]
  rfl

private theorem program_image : Airbender.SubwordMemory.programImage before [0] = some [entry] := by
  have bytes : (Cell.ram 0).read before = .ok entry.bits before := written_word_read _ 0 _
  have decoded : run (SailRV32.Functions.encdec_backwards entry.bits) before =
      .ok entry.instruction before := by with_unfolding_all rfl
  simp only [Airbender.SubwordMemory.programImage, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, bind, Option.bind]
  rfl

private theorem decoded : Airbender.SubwordMemory.Decoded trace [entry] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  change ∃ i, _
  exact ⟨⟨0, by decide⟩, by decide⟩

/-- Source/result bounds follow from the extracted public cells and the
    accepted native row, without a desired-read or output-bound premise. -/
theorem actual_native_bounds :
    (∀ actual ∈ trace.rows, ∀ port ∈ actual.ports,
      (readToken actual.assignment port).word.Bounded) ∧
    (∀ actual ∈ trace.rows, ∀ port ∈ actual.ports,
      (writeToken actual.columns actual.assignment port).word.Bounded) ∧
    (∀ token ∈ trace.terminalMemory, token.word.Bounded) :=
  Airbender.SubwordMemory.Proofs.native_value_bounds (by decide) (by decide)
    accepted boundary (Proofs.image_bounds image) rfl

/-- A real public RAM/GPR image, actual LBU decoding and native matching
    produce complete grouped Sail cell histories. -/
theorem actual_native_history :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row babyBearModulus Airbender.SubwordMemory.TraceKind)) (after : State),
      MemoryHistory trace history ∧ rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      Proofs.SailHistory cells
        (rows.flatMap fun row => (Proofs.rowEvents trace.memoryEpoch row).reverse) before after ∧
      Proofs.SailStateMatches cells history after := by
  apply Airbender.SubwordMemory.Proofs.decoded_native_history (by decide) (by decide)
    accepted boundary image (by decide) _ program_image decoded
  intro cell member
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp [Cell.Aligned]

end Tests.SubwordMemoryHistory
