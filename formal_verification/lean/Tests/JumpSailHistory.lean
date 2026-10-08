import Tests.JumpHistory
import Airbender.Proofs.JumpBranchSlt.Trace
import Airbender.Proofs.Trace.Terminal
import Airbender.Proofs.Sail.WordMemoryState

namespace Tests.JumpSailHistory
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

-- JAL x1,-4 and JAL x0,-4. All three x0 ports in the discarded form
-- retain the latest preceding native clock; public x1 starts at five.
def assignment (discarded : Bool) (i : Nat) : ZMod babyBearModulus :=
  if discarded && (i = 7 || i = 28 || i = 30) then 0
  else if discarded && i = 15 then 1
  else if discarded && i = 32 then 5
  else JumpHistory.assignment 5 false i

private def row (discarded : Bool) : Row babyBearModulus JumpBranchSlt.TraceKind :=
  ⟨.jumpBranchSlt, assignment discarded⟩

private def entry (discarded : Bool) : JumpBranchSlt.ProgramEntry :=
  ⟨0, if discarded then 0xffdff06f else 0xffdff0ef,
    .JAL (0x1ffffc, .Regidx (if discarded then 0 else 1)),
    ⟨(), 0, 0, (if discarded then 0 else 1), ⟨65532, 65535⟩,
      (if discarded then 17 else 1), 0⟩⟩

private def before (discarded : Bool) : State :=
  wordWriteState { (default : State) with regs :=
    Std.ExtDHashMap.emptyWithCapacity.insert .x1 (5 : BitVec 32) } 0 (entry discarded).bits

private def cells : List Cell := [.register 0, .register 1]
private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 5]

private def token (index clock value : Nat) : MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair index 0), (clock, 0), Nat.pair value 0⟩

private def trace (discarded : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus where
  rows := [row discarded]
  rom := rom
  initial := (row discarded).start
  terminal := (row discarded).finish
  initialMemory := seed
  terminalMemory := if discarded then [token 0 6 0, token 1 0 5]
    else [token 0 5 0, token 1 6 4]

private theorem constraints (discarded : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment discarded)) JumpBranchSlt.clockConstraints := by
  have core := Verification.holds_of_sublist (JumpHistory.constraints 5 false)
    (List.sublist_append_left JumpBranchSlt.importedConstraints
      JumpBranchSlt.importedConstraintsTimestampLookups)
  apply Verification.holds_append (left := JumpBranchSlt.importedConstraints)
    (right := JumpBranchSlt.importedConstraintsTimestampLookups)
  · cases discarded <;>
      simpa [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
        Lookup.Contains, Vector.map, Expression.eval, Verification.environment, assignment,
        JumpHistory.assignment, Tests.JumpTimestamp.assignment, Verification.range16,
        Verification.pairLookup, Verification.jumpCleanup] using core
  · cases discarded <;>
      simp [JumpBranchSlt.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    all_goals repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment,
      JumpHistory.assignment, Tests.JumpTimestamp.assignment]
    all_goals decide

private theorem accepted (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : Accepted (trace discarded rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact constraints discarded
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    cases discarded <;> rfl
  · exact List.Perm.swap _ _ []
  · cases discarded <;> dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns,
      row, JumpBranchSlt.importedConstraintsMemoryPorts, JumpBranchSlt.importedConstraintsTraceColumns]
    all_goals decide

private theorem boundary (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) : ClockBoundary (trace discarded rom) := by
  constructor
  · cases discarded <;>
      change 4 < timestampBase ∧ 0 < timestampBase
    all_goals constructor <;> decide
  · cases discarded <;> change 4 % 4 = 0
    all_goals decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

private theorem image (discarded : Bool) :
    initialImage (before discarded) cells = some seed := by
  have zero : (Cell.register 0).read (before discarded) = .ok 0 (before discarded) := rfl
  have one : (Cell.register 1).read (before discarded) = .ok 5 (before discarded) := by
    apply read_register
    simp [before, wordWriteState]
  simp only [initialImage, cells, seed, List.mapM_cons, List.mapM_nil, zero, one]
  rfl

private theorem program_image (discarded : Bool) :
    JumpBranchSlt.programImage (before discarded) [0] = some [entry discarded] := by
  have bytes : (Cell.ram 0).read (before discarded) = .ok (entry discarded).bits (before discarded) :=
    written_word_read _ 0 (entry discarded).bits
  simp only [List.mapM_cons, List.mapM_nil, programEntryWith, bytes, bind, Option.bind]
  cases discarded <;> rfl

private theorem decoded (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.Decoded (trace discarded rom) [entry discarded] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  cases discarded <;> change ∃ i, _
  all_goals exact ⟨⟨0, by decide⟩, by decide⟩

/-- Public extraction and actual Sail decoding discharge x0 preservation for
    both an ordinary destination and a discarded write; no zero value is assumed. -/
theorem actual_zero_law (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Trace.Proofs.ZeroPreserving (trace discarded rom) :=
  JumpBranchSlt.Proofs.zero_preserving (by decide) (accepted discarded rom)
    (program_image discarded) (decoded discarded rom)

/-- Native matching, actual initial GPRs and the public decoded bytes produce
    Sail's real cell effects and the exact terminal x1 read. PC stepping is separate. -/
theorem actual_terminal_register (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ (rows : List (Row babyBearModulus JumpBranchSlt.TraceKind)) (after : State),
      rows.Perm (trace discarded rom).rows ∧
      Proofs.SailHistory cells
        (rows.flatMap fun row => (Proofs.rowEvents (trace discarded rom).memoryEpoch row).reverse)
        (before discarded) after ∧
      run (SailRV32.Functions.rX_bits (.Regidx 1)) after =
        .ok (if discarded then 5 else 4) after := by
  obtain ⟨history, rows, after, consistent, permutation, _, execution, realized⟩ :=
    JumpBranchSlt.Proofs.decoded_native_history (by decide) (by decide)
      (accepted discarded rom) (boundary discarded rom) (image discarded) (by decide)
      (by intro cell member; simp [cells] at member; rcases member with rfl | rfl <;> trivial)
      (program_image discarded) (decoded discarded rom)
  have terminal := Proofs.terminal_sail_reads (by decide) (by decide)
    (accepted discarded rom) (boundary discarded rom) (image discarded) (by decide) consistent realized
  let sink := token 1 (if discarded then 0 else 6) (if discarded then 5 else 4)
  have member : sink ∈ (trace discarded rom).terminalMemory := by
    cases discarded <;> simp [trace, sink]
  obtain ⟨cell, present, address, read⟩ := terminal sink member
  have same : cell = Cell.register 1 := by
    apply Proofs.cell_address_injective
    exact address
  subst cell
  refine ⟨rows, after, permutation, execution, ?_⟩
  cases discarded <;>
    simpa [Cell.read, sink, token, Proofs.memoryWord, Nat.unpair_pair, Word.toBitVec, Word.value, limbBase] using read

end Tests.JumpSailHistory
