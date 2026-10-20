import Slop.Trace.Claims
import Slop.Trace.OracleExecution

namespace Tests.NonDeterminismDecoder
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

-- Independent public bytes: CSRRW x1,0x7C0,x0; CSRRW x0,0x7C0,x1.
private def before : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity).insert .x1 (0 : BitVec 32) |>.insert .PC 0
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 0 (0xF3 : BitVec 8)
      |>.insert 1 0x10 |>.insert 2 0 |>.insert 3 0x7C
      |>.insert 4 0x73 |>.insert 5 0x90 |>.insert 6 0 |>.insert 7 0x7C }

private def readEntry : ProgramEntry :=
  ⟨0, 0x7C0010F3, .CSRReg (0x7C0, .Regidx 0, .Regidx 1, .CSRRW),
    ⟨.addSub, 0, 0, 1, ⟨0, 0⟩, 256, 0⟩⟩
private def writeEntry : ProgramEntry :=
  ⟨4, 0x7C009073, .CSRReg (0x7C0, .Regidx 1, .Regidx 0, .CSRRW),
    ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩

private theorem read_decoding : SailRV32.Functions.encdec_backwards readEntry.bits =
    (.pure readEntry.instruction : SailRV32.SailM SailRV32.instruction) := by
  dsimp only [readEntry, writeEntry]
  with_unfolding_all rfl

private theorem write_decoding : SailRV32.Functions.encdec_backwards writeEntry.bits =
    (.pure writeEntry.instruction : SailRV32.SailM SailRV32.instruction) := by
  dsimp only [readEntry, writeEntry]
  with_unfolding_all rfl

theorem original_read_decoder (state : State) :
    run (SailRV32.Functions.encdec_backwards 0x7C0010F3) state =
      .ok readEntry.instruction state := by
  change run (SailRV32.Functions.encdec_backwards readEntry.bits) state = _
  rw [read_decoding]
  rfl

theorem original_write_decoder (state : State) :
    run (SailRV32.Functions.encdec_backwards 0x7C009073) state =
      .ok writeEntry.instruction state := by
  change run (SailRV32.Functions.encdec_backwards writeEntry.bits) state = _
  rw [write_decoding]
  rfl

private theorem bytes (write : Bool) :
    (Cell.ram (if write then 4 else 0)).read before =
      .ok (if write then writeEntry.bits else readEntry.bits) before := by
  cases write <;>
    simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, readEntry, writeEntry, Std.ExtHashMap.getElem_insert]

theorem public_image : programImageWith NonDeterminism.decoderFields before [0, 4] =
    some [readEntry, writeEntry] := by
  have read := bytes false
  have write := bytes true
  simp only [Bool.false_eq_true, ite_false, ite_true] at read write
  simp only [programImageWith, List.mapM_cons, List.mapM_nil, programEntryWith,
    read, write, read_decoding, write_decoding, bind, Option.bind]
  rfl

private def assignment : Nat → ZMod babyBearModulus
  | 2 | 19 | 27 => 4
  | 4 | 7 | 18 | 42 | 43 | 44 => 1
  | 21 => 8
  | 33 => 0x5678
  | 34 => 0x1234
  | _ => 0

private def row : Row babyBearModulus := ⟨.addSub, assignment⟩
private def regToken (index time value : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (time, 0), value⟩
private def trace : Data babyBearModulus where
  rows := [row]
  rom := ROM.table [] []
  initial := row.start
  terminal := row.finish
  initialMemory := [regToken 0 0 0, regToken 1 0 0]
  terminalMemory := [regToken 0 5 0, regToken 1 6 (Nat.pair 0x5678 0x1234)]

theorem native_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact native_constraints
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · decide

private theorem membership : Decoded trace [readEntry, writeEntry] := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  change ∃ i : Fin 2, _
  exact ⟨0, by decide⟩

/-- Source bytes, original CSR instruction, PC, indices and selector 8 are
    recovered from public decoding and native query membership. -/
theorem fetched_read : row.Fetched before NonDeterminism.decoderFields :=
  NonDeterminism.decoder_soundness accepted public_image membership row (by simp [trace])

theorem read_selector : ∀ i : Fin 9,
    assignment (#[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) = if i.val = 8 then 1 else 0 := by
  have bits := Proofs.query_selectors_of_bound (p := babyBearModulus) (by decide)
    accepted (row := row) (by simp [trace]) (entry := readEntry) (by decide) (by decide)
  intro i
  have checked := bits i
  fin_cases i <;>
    simpa [readEntry, row, Row.decoderColumns, AddSub.importedConstraintsDecoderColumns,
      Nat.testBit, Nat.shiftRight_eq_div_pow] using checked

theorem malformed_csr_rejected :
    NonDeterminism.decoderFields (.CSRReg (0x7C0, .Regidx 1, .Regidx 1, .CSRRW)) = none ∧
    NonDeterminism.decoderFields (.CSRReg (0x7C0, .Regidx 0, .Regidx 0, .CSRRW)) = none ∧
    NonDeterminism.decoderFields (.CSRReg (0x7C1, .Regidx 0, .Regidx 1, .CSRRW)) = none ∧
    NonDeterminism.decoderFields (.CSRReg (0x7C0, .Regidx 0, .Regidx 1, .CSRRS)) = none ∧
    NonDeterminism.decoderFields (.CSRImm (0x7C0, 0, .Regidx 1, .CSRRW)) = none := by
  repeat' first | apply And.intro | rfl

private theorem clocks : ClockBoundary trace := by
  constructor
  · constructor <;> decide
  · decide
  · intro token member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

/-- The accepted native read consumes the independent first response and leaves
    the unused suffix; its position is derived rather than supplied by a witness. -/
theorem single_native_consumption :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      ∃ rest, [0x12345678, 0xbeef] = NonDeterminism.consumed rows ++ rest := by
  apply NonDeterminism.native_consumption accepted clocks
  intro actual member _
  have same := List.mem_singleton.mp member
  subst actual
  decide

private def cells : List Cell := [.register 0, .register 1]

private theorem initial_image : initialImage before cells = some trace.initialMemory := by
  have one : (Cell.register 1).read before = .ok 0 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  change List.mapM _ [Cell.register 0, Cell.register 1] = _
  simp only [List.mapM_cons, List.mapM_nil, one, bind, Option.bind]
  rfl

/-- The CSR read enters the same native offline-memory/Sail history proof as
    arithmetic. Its actual final x1 value is derived; x0/read values are not premises. -/
theorem native_register_history :
    ∃ after, (Cell.register 1).read after = .ok 0x12345678 after := by
  obtain ⟨history, events, _, after, consistent, _, _, _, matched⟩ :=
    Proofs.decoded_sail_history NonDeterminism.Proofs.decoderRules (by decide) (by decide)
      accepted clocks initial_image (by decide) (by
        intro cell member
        simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> trivial) public_image membership
  have terminal := Proofs.terminal_sail_reads (by decide) (by decide) accepted clocks
    initial_image (by decide) consistent matched
      (regToken 1 6 (Nat.pair 0x5678 0x1234)) (by simp [trace])
  obtain ⟨cell, _, address, read⟩ := terminal
  have same : cell = Cell.register 1 := Proofs.cell_address_injective address
  subst cell
  exact ⟨after, by simpa [regToken, memoryWord, Nat.unpair_pair, Word.toBitVec, Word.value, limbBase] using read⟩

/-- Native CSR register effects and PC retirement are one actual reference
    step, consuming exactly the first independently supplied external word. -/
theorem native_read_step [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :
    ∃ after, NonDeterminism.Step [0x12345678] [readEntry, writeEntry]
      (before, 0) (after, 1) ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 4 after := by
  obtain ⟨_, rows, after, _, permutation, _, history, _⟩ :=
    Proofs.decoded_row_history NonDeterminism.Proofs.decoderRules (by decide) (by decide)
      accepted clocks initial_image (by decide) (by
        intro cell member
        simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> trivial) public_image membership
  have single : rows = [row] := List.perm_singleton.mp permutation
  rw [single] at history
  simp only [List.flatMap_cons] at history
  have current : run (SailRV32.Functions.get_arch_pc ()) before = .ok 0 before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  have currentNative : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok row.start.word.toBitVec before := current
  have checked := NonDeterminism.Proofs.read_row_execution (by decide) (by decide)
    accepted (by
      change 0 < limbBase ∧ 0 < limbBase
      constructor <;> decide) (by simp [trace, row])
    (entry := readEntry) (rd := 1) rfl (by decide) history currentNative
  have value : NonDeterminism.response row = 0x12345678 := by decide
  have next : row.finish.word.toBitVec = 4 := by decide
  change run (normalStep (writeResult (.Regidx 1) (Word.ofBitVec (NonDeterminism.response row))))
    before = .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) at checked
  rw [value, next] at checked
  refine ⟨retiredState after 4, ?_, Proofs.retired_state_pc after 4⟩
  refine ⟨readEntry, by simp, Proofs.program_sources public_image readEntry (by simp),
    current, writeResult (.Regidx 1) (Word.ofBitVec 0x12345678), ?_, checked⟩
  rfl

private def later : Row babyBearModulus := ⟨.addSub, fun column =>
  if column = 2 then 8 else if column = 33 then 0x9999 else assignment column⟩
private def hint : Row babyBearModulus := ⟨.addSub, fun column =>
  if column = 2 then 12 else if column = 18 then 0 else assignment column⟩
private def reordered : Data babyBearModulus := { trace with rows := [row, hint, later] }

-- These three-row fixtures check consumption/order only, not native acceptance.
theorem clock_positions :
    NonDeterminism.readIndex reordered row = 0 ∧
    NonDeterminism.readIndex reordered later = 1 := by decide

theorem ordered_responses :
    NonDeterminism.consumed [hint, later, row] = [0x12345678, 0x12349999] := by decide

theorem storage_order_does_not_change_position :
    NonDeterminism.readIndex { reordered with rows := [hint, later, row] } later =
      NonDeterminism.readIndex reordered later := by
  apply NonDeterminism.Proofs.read_index_permutation
  exact (List.Perm.cons hint (List.Perm.swap later row []).symm) |>.trans
    (List.Perm.swap hint row [later]).symm

theorem chronological_ports :
    NonDeterminism.StreamPorts reordered [0x12345678, 0x12349999] := by
  intro actual member read
  simp only [reordered, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · decide
  · have absent : ¬ NonDeterminism.isRead hint = true := by decide
    exact False.elim (absent read)
  · decide

theorem swapped_stream_rejected :
    ¬ NonDeterminism.StreamPorts reordered [0x12349999, 0x12345678] := by
  intro ports
  have wrong := ports row (by simp [reordered]) (by decide)
  have unequal : (([0x12349999, 0x12345678] : List (BitVec 32))[NonDeterminism.readIndex reordered row]?) ≠ some (NonDeterminism.response row) := by decide
  exact unequal wrong

theorem short_stream_rejected :
    ¬ NonDeterminism.StreamPorts reordered [0x12345678] := by
  intro ports
  have missing := ports later (by simp [reordered]) (by decide)
  have absent : ([0x12345678] : List (BitVec 32))[NonDeterminism.readIndex reordered later]? = none := by decide
  change ([0x12345678] : List (BitVec 32))[NonDeterminism.readIndex reordered later]? = _ at missing
  rw [absent] at missing
  cases missing

end Tests.NonDeterminismDecoder
