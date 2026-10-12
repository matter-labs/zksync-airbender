import Airbender.Proofs.ShiftBinop.Execution
import Airbender.Proofs.ShiftBinop.Claims
import Airbender.Proofs.Sail.WordMemoryState
import Tests.ShiftBinopTimestamp

namespace Tests.ShiftBinopImmediate
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

-- XORI x1,x0,-1: exercise both packed immediate bytes and the upper sign bytes.
private def assignment (i : Nat) : ZMod babyBearModulus :=
  if i = 8 ∨ i = 9 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨
      i = 52 ∨ i = 53 ∨ i = 57 ∨ i = 58 ∨ i = 66 ∨ i = 67 ∨
      i = 75 ∨ i = 76 ∨ i = 84 ∨ i = 85 then 255
  else if i = 31 ∨ i = 32 then 65535
  else Tests.ShiftBinopTimestamp.assignment false i

theorem constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
    Airbender.ShiftBinop.importedConstraints := by
  simp [Airbender.ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment, Tests.ShiftBinopTimestamp.assignment,
    Tests.ShiftBinop.row]
  repeat' apply And.intro
  all_goals solve
    | decide
    | (apply Verification.range16_contains; decide)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[255, 255, 0, 0, 0, 0, 0, 0, 0, 3] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨256, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨256, by decide⟩ =
           (#v[255, 255, 0, 0, 0, 0, 0, 0, 0, 3] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)
    | (with_unfolding_all change ∃ i : Fin 524545,
         (#v[0, 255, 255, 0, 0, 0, 0, 0, 0, 4] : Vector (ZMod babyBearModulus) 10) =
           (Verification.shiftBinopRow i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       refine ⟨⟨512, by decide⟩, ?_⟩
       have shape : Verification.shiftBinopRow ⟨512, by decide⟩ =
           (#v[0, 255, 255, 0, 0, 0, 0, 0, 0, 4] : Vector Nat 10) := by decide
       rw [shape]
       apply Vector.ext
       intro j bound
       rw [Vector.getElem_map]
       interval_cases j <;> norm_num)

theorem effective_operand :
    ∀ i : Fin 4, assignment (25 + i.val) +
      (if i.val = 0 then assignment 8 else if i.val = 1 then assignment 9 else assignment 35) =
      ((SailRV32.Functions.sign_extend (m := 32) (4095#12)).extractLsb'
        (8 * i.val) 8).toNat :=
  Airbender.ShiftBinop.Proofs.binary_immediate_right_bytes (by decide) constraints
    ⟨by decide, by decide⟩ 4 (Or.inl rfl) (by decide) 4095#12
    ⟨by decide, by decide⟩ (by decide)


private theorem clock_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) Airbender.ShiftBinop.clockConstraints := by
  apply Verification.holds_append (left := Airbender.ShiftBinop.importedConstraints)
    (right := Airbender.ShiftBinop.importedConstraintsTimestampLookups)
  · exact constraints
  · simp [Airbender.ShiftBinop.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, assignment,
      Tests.ShiftBinopTimestamp.assignment, Tests.ShiftBinop.row]
    all_goals decide

private def entry : Airbender.ShiftBinop.ProgramEntry :=
  ⟨65532, 0xfff04093, .ITYPE (4095#12, .Regidx 0, .Regidx 1, .XORI),
    ⟨(), 0, 0, 1, ⟨255, 255⟩, 2, 4⟩⟩

private def before : State := wordWriteState
  { (default : State) with regs :=
    ((default : State).regs.insert .x1 (0 : BitVec 32)).insert .PC (65532 : BitVec 32) }
  65532 entry.bits

private def cells : List Cell := [.register 0, .register 1]
private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 0]
private def row : Row babyBearModulus Airbender.ShiftBinop.TraceKind :=
  ⟨.shiftBinop, assignment⟩

private def trace (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Airbender.ShiftBinop.NativeTrace babyBearModulus where
  rows := [row]
  rom := rom
  initial := row.start
  terminal := row.finish
  initialMemory := seed
  terminalMemory := [⟨(Cell.register 0).addressCode, (5, 0), 0⟩,
    ⟨(Cell.register 1).addressCode, (6, 0), Nat.pair 65535 65535⟩]

private theorem accepted (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Accepted (trace rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact clock_constraints
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
      SailHistory cells
        (rows.flatMap fun row => (Trace.rowEvents (trace rom).memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after := by
  apply Airbender.ShiftBinop.Proofs.decoded_native_history (by decide) (by decide)
    (accepted rom) (boundary rom) image (by decide) _ program_image (decoded rom)
  intro cell member
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> trivial

/-- Actual imported acceptance, public decoding and grouped history feed the
    native row theorem through original Sail execution and retirement. -/
theorem actual_immediate_retirement (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after,
      run (normalStep (SailRV32.Functions.execute_ITYPE (4095#12) (.Regidx 0) (.Regidx 1) .XORI))
        (retiredState before 65532) = .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after 65536) := by
  obtain ⟨_, rows, after, _, permutation, _, native, _⟩ := actual_native_history rom
  have single : rows = [row] := List.perm_singleton.mp permutation
  rw [single] at native
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at native
  have query : Airbender.ShiftBinop.decoderQuery row.assignment = entry.query := by decide
  have checked := Airbender.ShiftBinop.Proofs.row_execution (by decide) (by decide)
    (by decide) (accepted rom) (boundary rom) image program_image (decoded rom)
    (by simp [trace]) (by simp) query .xor true 4095#12 0 0 1 rfl native
  refine ⟨after, ?_⟩
  simpa [entry, row, assignment, Tests.ShiftBinopTimestamp.assignment, Tests.ShiftBinop.row,
    Airbender.ShiftBinop.execution, Airbender.ShiftBinop.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, Airbender.ShiftBinop.importedConstraintsMemoryPorts,
    MemoryPort.readCode, memoryWord, WordColumns.code, WordColumns.evaluate,
    Word.toBitVec, Word.value, Nat.unpair_pair, limbBase,
    show (65532 : ZMod babyBearModulus).val = 65532 by decide,
    show (1 : ZMod babyBearModulus).val = 1 by decide] using checked


/-- Public fetch/decoding and native histories compose from the unchanged
    public state through original Sail execution to the terminal PC. -/
theorem actual_immediate_trace [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after, Airbender.ShiftBinop.SailTrace [entry] before after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 65536 after := by
  have initialPC : initialState before (4, 0) = some (trace rom).initial := by
    have read : run (SailRV32.Functions.get_arch_pc ()) before = .ok 65532 before := by
      apply read_register
      simp [before, wordWriteState]
    rw [initialState, read]
    rfl
  have inputs : Airbender.ShiftBinop.ExecutionBoundary (trace rom) before cells [entry] := {
    distinct := by decide
    aligned := by intro cell member; simp [cells] at member; rcases member with rfl | rfl <;> trivial
    image := image
    initialPC := ⟨(4, 0), initialPC⟩
    programImage := ⟨[65532], program_image⟩
    clocks := boundary rom
  }
  obtain ⟨after, execution, pc, _⟩ := Airbender.ShiftBinop.trace_soundness
    (by decide) (by decide) (by decide) inputs (accepted rom) (decoded rom)
  exact ⟨after, execution, pc⟩

end Tests.ShiftBinopImmediate
