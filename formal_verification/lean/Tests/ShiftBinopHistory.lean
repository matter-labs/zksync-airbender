import Tests.ShiftBinopTimestamp
import Airbender.Proofs.ShiftBinop.Trace
import Airbender.Proofs.Sail.WordMemoryState

namespace Tests.ShiftBinopHistory
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private def entry : Airbender.ShiftBinop.ProgramEntry :=
  ⟨65532, 0x000040b3, .RTYPE (.Regidx 0, .Regidx 0, .Regidx 1, .XOR),
    ⟨(), 0, 0, 1, ⟨0, 0⟩, 2, 4⟩⟩

private def before : State := wordWriteState
  { (default : State) with regs :=
    ((default : State).regs.insert .x1 (0 : BitVec 32)).insert .PC (65532 : BitVec 32) }
  65532 entry.bits

private def cells : List Cell := [.register 0, .register 1]
private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 0]
private def row : Row babyBearModulus Airbender.ShiftBinop.TraceKind :=
  ⟨.shiftBinop, Tests.ShiftBinopTimestamp.assignment false⟩

private def trace (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Airbender.ShiftBinop.NativeTrace babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := seed
  terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), 0⟩,
    ⟨(Cell.register 1).addressCode, (6, 0), 0⟩]

private theorem accepted (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Accepted (trace rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact Tests.ShiftBinopTimestamp.constraints false
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, row,
      Airbender.ShiftBinop.importedConstraintsMemoryPorts,
      Airbender.ShiftBinop.importedConstraintsTraceColumns]
    decide

private theorem boundary (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ClockBoundary (trace rom) := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

private theorem image : initialImage before cells = some seed := by
  have zero : (Cell.register 0).read before = .ok 0 before := rfl
  have one : (Cell.register 1).read before = .ok 0 before := by
    apply read_register
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
  simp only [initialImage, cells, seed, List.mapM_cons, List.mapM_nil, zero, one]
  rfl

private theorem program_image : Airbender.ShiftBinop.programImage before [65532] = some [entry] := by
  have bytes : (Cell.ram 65532).read before = .ok entry.bits before := written_word_read _ 65532 _
  have decoded : run (SailRV32.Functions.encdec_backwards entry.bits) before =
      .ok entry.instruction before := by with_unfolding_all rfl
  simp only [Airbender.ShiftBinop.programImage, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, decoded, bind, Option.bind]
  rfl

private theorem decoded (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Airbender.ShiftBinop.Decoded (trace rom) [entry] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  change ∃ i, _
  exact ⟨⟨0, by decide⟩, by decide⟩

/-- Native byte ports, alias refreshes, public initialization and actual
    Sail decoding produce a complete grouped register history. -/
theorem actual_native_history (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ (history : TimestampSortedMemoryAccessList)
      (rows : List (Row babyBearModulus Airbender.ShiftBinop.TraceKind)) (after : State),
      MemoryHistory (trace rom) history ∧ rows.Perm (trace rom).rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      Proofs.SailHistory cells
        (rows.flatMap fun row => (Proofs.rowEvents (trace rom).memoryEpoch row).reverse) before after ∧
      Proofs.SailStateMatches cells history after := by
  apply Airbender.ShiftBinop.Proofs.decoded_native_history (by decide) (by decide)
    (accepted rom) (boundary rom) image (by decide) _ program_image (decoded rom)
  intro cell member
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> trivial

end Tests.ShiftBinopHistory
