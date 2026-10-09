import Airbender.Proofs.JumpBranchSlt.Execution
import Tests.JumpHistory
import Airbender.Proofs.JumpBranchSlt.Trace
import Airbender.Proofs.JumpBranchSlt.Values
import Airbender.Proofs.Trace.Terminal
import Airbender.Proofs.Sail.WordMemoryState
import Airbender.Proofs.Sail.PC

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
    (((Std.ExtDHashMap.emptyWithCapacity.insert .x1 (5 : BitVec 32)).insert
      .PC (0 : BitVec 32)).insert .misa (0 : BitVec 32)) } 0 (entry discarded).bits

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
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
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

/-- All actual native operand and terminal-register words are canonical, for
    ordinary and discarded destinations, without a supplied operand bound. -/
theorem register_value_bounds (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    (∀ actual ∈ (trace discarded rom).rows, ∀ port ∈ actual.ports,
      (readToken actual.assignment port).word.Bounded) ∧
      (∀ actual ∈ (trace discarded rom).rows, ∀ port ∈ actual.ports,
        (writeToken actual.columns actual.assignment port).word.Bounded) ∧
      (∀ actual ∈ (trace discarded rom).terminalMemory, actual.word.Bounded) :=
  JumpBranchSlt.Proofs.native_value_bounds (by decide) (by decide)
    (accepted discarded rom) (boundary discarded rom) (image discarded)
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

/-- Both ordinary and discarded JAL writes execute the original Sail clause
    through the actual native history and retire to the full 32-bit target. -/
theorem actual_jal_retirement (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after,
      initialState (Proofs.retiredState (before discarded) 0) (4, 0) =
        some (trace discarded rom).initial ∧
      run (normalStep (SailRV32.Functions.execute_JAL 0x1ffffc
        (.Regidx (if discarded then 0 else 1)))) (Proofs.retiredState (before discarded) 0) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (Proofs.retiredState after 0xfffffffc) ∧
      run (SailRV32.Functions.rX_bits (.Regidx 1)) after =
        .ok (if discarded then 5 else 4) after := by
  obtain ⟨rows, after, permutation, history, read⟩ := actual_terminal_register discarded rom
  have single : rows = [row discarded] := by
    simpa only [trace] using List.perm_singleton.mp permutation
  subst rows
  have native : Proofs.SailHistory cells
      (JumpBranchSlt.Proofs.nativeEvents (trace discarded rom).memoryEpoch
        (assignment discarded)).reverse (before discarded) after := by
    simpa [Proofs.rowEvents, row, Row.ports, Row.columns] using history
  have checked := JumpBranchSlt.Proofs.jump_rebased_step (entry := entry discarded) (by decide) (by decide)
    (accepted discarded rom) (boundary discarded rom) (image discarded)
    (program_image discarded) (decoded discarded rom)
    (by cases discarded <;> change (⟨65532, 65535⟩ : Word).Bounded
        all_goals constructor <;> decide)
    (by cases discarded <;> change 0 % 4 = 0
        all_goals decide)
    (by simp [trace, row]) (by simp) (by cases discarded <;> decide)
    (.jal 0x1ffffc) 0 (if discarded then 0 else 1) rfl native (.nil _)
    (by refine ⟨0, ?_⟩; simp [before, wordWriteState])
    (by intro impossible; cases impossible)
  refine ⟨after, ?_, ?_, read⟩
  · rw [initialState, Proofs.retired_state_pc (before discarded) 0]
    cases discarded <;> rfl
  · cases discarded <;>
      norm_num [assignment, JumpHistory.assignment, JumpTimestamp.assignment,
        Word.toBitVec, Word.value, limbBase, ZMod.val_ofNat, babyBearModulus] at checked ⊢
    all_goals exact checked

-- Flip the high-PC wrap bit and use its field-aliased result. Neither the
-- incoming decoder nor the register history ranges the external terminal PC.
private def noncanonicalAssignment (i : Nat) : ZMod babyBearModulus :=
  if i = 17 then -1 else if i = 40 then 1 else assignment false i

private def noncanonicalRow : Row babyBearModulus JumpBranchSlt.TraceKind :=
  ⟨.jumpBranchSlt, noncanonicalAssignment⟩

private def noncanonicalTrace (rom : Table (ZMod babyBearModulus) (fields 9)) :
    JumpBranchSlt.NativeTrace babyBearModulus :=
  { trace false rom with rows := [noncanonicalRow], terminal := noncanonicalRow.finish }

private theorem noncanonical_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment noncanonicalAssignment) JumpBranchSlt.clockConstraints := by
  have core := Verification.holds_of_sublist (constraints false)
    (List.sublist_append_left JumpBranchSlt.importedConstraints
      JumpBranchSlt.importedConstraintsTimestampLookups)
  apply Verification.holds_append (left := JumpBranchSlt.importedConstraints)
    (right := JumpBranchSlt.importedConstraintsTimestampLookups)
  · have high : (65535 + 1 + -65536 : ZMod babyBearModulus) = 0 := by decide
    simpa [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Lookup.Contains, Vector.map, Expression.eval, Verification.environment,
      noncanonicalAssignment, assignment, JumpHistory.assignment, Tests.JumpTimestamp.assignment,
      Verification.range16, Verification.pairLookup, Verification.jumpCleanup, high] using core
  · have timestamps := Verification.holds_of_sublist (constraints false)
      (List.sublist_append_right JumpBranchSlt.importedConstraints
        JumpBranchSlt.importedConstraintsTimestampLookups)
    simpa [JumpBranchSlt.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
      Lookup.Contains, timestampLookup, Vector.map, Expression.eval, Verification.environment,
      noncanonicalAssignment] using timestamps

private theorem initial_pc (rom : Table (ZMod babyBearModulus) (fields 9)) :
    initialState (before false) (4, 0) = some (trace false rom).initial := by
  have pc : run (SailRV32.Functions.get_arch_pc ()) (before false) = .ok 0 (before false) := by
    change run (SailRV32.readReg .PC) (before false) = _
    apply read_register
    simp [before, wordWriteState, Std.ExtDHashMap.get?_insert]
  rw [initialState, pc]
  rfl

/-- Actual incoming decoding plus canonical termination bounds the whole row. -/
theorem decoded_pc_bounds (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∀ actual ∈ (trace discarded rom).rows,
      actual.start.word.Bounded ∧ actual.finish.word.Bounded := by
  apply JumpBranchSlt.Proofs.trace_pc_bounds (by decide) (accepted discarded rom)
    (decoded discarded rom)
  cases discarded <;> change (⟨65532, 65535⟩ : Word).Bounded
  all_goals constructor <;> decide

/-- Native matching propagates public initial alignment to the entire trace. -/
theorem decoded_pc_alignment (discarded : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    (∀ actual ∈ (trace discarded rom).rows,
      actual.start.word.lo % 4 = 0 ∧ actual.finish.word.lo % 4 = 0) ∧
      (trace discarded rom).terminal.word.lo % 4 = 0 :=
  JumpBranchSlt.Proofs.trace_pc_alignment (by decide) (accepted discarded rom)
    (by cases discarded <;> rfl)

/-- Even complete native matching, the public Sail-decoded JAL and the actual
    public GPR seed admit this row. Terminal PC normalization is still external. -/
theorem noncanonical_native_accepted (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Accepted (noncanonicalTrace rom) ∧
      JumpBranchSlt.Decoded (noncanonicalTrace rom) [entry false] ∧
      ClockBoundary (noncanonicalTrace rom) ∧
      initialImage (before false) cells = some (noncanonicalTrace rom).initialMemory ∧
      initialState (before false) (4, 0) = some (noncanonicalTrace rom).initial ∧
      JumpBranchSlt.programImage (before false) [0] = some [entry false] := by
  refine ⟨?_, ?_, ?_, image false, initial_pc rom, program_image false⟩
  · constructor
    · intro actual member
      simp only [noncanonicalTrace, List.mem_singleton] at member
      subst actual
      exact noncanonical_constraints
    · intro actual member
      simp only [noncanonicalTrace, List.mem_singleton] at member
      subst actual
      rfl
    · exact List.Perm.swap _ _ []
    · dsimp [noncanonicalTrace, trace, Row.reads, Row.writes, Row.ports, Row.columns,
        row, noncanonicalRow, JumpBranchSlt.importedConstraintsMemoryPorts,
        JumpBranchSlt.importedConstraintsTraceColumns]
      decide
  · intro actual member
    simp only [noncanonicalTrace, List.mem_singleton] at member
    subst actual
    change ∃ i, _
    exact ⟨⟨0, by decide⟩, by decide⟩
  · constructor
    · exact (boundary false rom).initial
    · exact (boundary false rom).aligned
    · exact (boundary false rom).memory

/-- Its encoded terminal word disagrees with JAL's original Sail sign-extended
    offset from PC zero. This is a richer-row/termination gap, not a claim about
    the full system's teardown argument. -/
theorem noncanonical_terminal_mismatch (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ¬ (noncanonicalTrace rom).terminal.word.Bounded ∧
      (noncanonicalTrace rom).terminal.word.toBitVec ≠
        (SailRV32.Functions.sign_extend (m := 32) (0x1ffffc : BitVec 21)) := by
  change ¬ (⟨65532, (-1 : ZMod babyBearModulus).val⟩ : Word).Bounded ∧ _
  constructor
  · intro bounded
    exact (by decide : ¬ (-1 : ZMod babyBearModulus).val < limbBase) bounded.2
  · change (⟨65532, (-1 : ZMod babyBearModulus).val⟩ : Word).toBitVec ≠ _
    decide

/-- Register-word propagation still holds for the malformed terminal-PC row;
    it does not assume or repair that missing endpoint binding. -/
theorem noncanonical_register_bounds (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∀ actual ∈ (noncanonicalTrace rom).rows, ∀ port ∈ actual.ports,
      (readToken actual.assignment port).word.Bounded := by
  obtain ⟨accepted, decoded, clocks, image, _, program⟩ := noncanonical_native_accepted rom
  exact (JumpBranchSlt.Proofs.native_value_bounds (by decide) (by decide)
    accepted clocks image program decoded).1

end Tests.JumpSailHistory
