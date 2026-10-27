import Slop.Sail.ResetState
import Tests.TraceExecution

namespace Tests.OracleTrace
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

-- Read x1; ADDI x2,x1,1; emit an unproved hint from x2. Rows are deliberately
-- stored out of execution order. Only the read consumes the independent stream.
private def before : State :=
  { Tests.TraceExecution.before with
    regs := Tests.TraceExecution.before.regs.insert .x1 (0 : BitVec 32)
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 0 (0xF3 : BitVec 8)
      |>.insert 1 0x10 |>.insert 2 0 |>.insert 3 0x7C
      |>.insert 4 0x13 |>.insert 5 0x81 |>.insert 6 0x10 |>.insert 7 0
      |>.insert 8 0x73 |>.insert 9 0x10 |>.insert 10 1 |>.insert 11 0x7C }

private def readEntry : ProgramEntry :=
  ⟨0, 0x7C0010F3, .CSRReg (0x7C0, .Regidx 0, .Regidx 1, .CSRRW),
    ⟨.addSub, 0, 0, 1, ⟨0, 0⟩, 256, 0⟩⟩
private def addEntry : ProgramEntry :=
  ⟨4, 0x00108113, .ITYPE (1, .Regidx 1, .Regidx 2, .ADDI),
    ⟨.addSub, 1, 0, 2, ⟨1, 0⟩, 1, 0⟩⟩
private def hintEntry : ProgramEntry :=
  ⟨8, 0x7C011073, .CSRReg (0x7C0, .Regidx 2, .Regidx 0, .CSRRW),
    ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩⟩
private def program := [readEntry, addEntry, hintEntry]

private def readAssignment : Nat → ZMod babyBearModulus
  | 2 | 19 | 27 => 4
  | 4 | 7 | 18 | 42 | 43 | 44 => 1
  | 21 => 8
  | 33 => 0x5678
  | 34 => 0x1234
  | _ => 0
private def addAssignment : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 19 => 8
  | 21 => 12
  | 4 | 5 | 8 | 10 | 42 | 43 | 44 => 1
  | 7 => 2
  | 23 => 6
  | 27 => 5
  | 25 => 0x5678
  | 26 | 34 => 0x1234
  | 33 => 0x5679
  | _ => 0
private def hintAssignment : Nat → ZMod babyBearModulus
  | 0 => 8
  | 2 | 19 | 27 => 12
  | 21 => 16
  | 4 | 10 | 42 | 43 | 44 => 1
  | 23 => 9
  | 35 => 13
  | _ => 0
private def readRow : Row babyBearModulus := ⟨.addSub, readAssignment⟩
private def addRow : Row babyBearModulus := ⟨.addSub, addAssignment⟩
private def hintRow : Row babyBearModulus := ⟨.addSub, hintAssignment⟩

private def regToken (index time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (time, 0), Nat.pair lo hi⟩
private def cells := Tests.TraceExecution.cells
private def seed : List (MemoryToken babyBearModulus) := ROMView.nativeBootImage cells
private def trace : Data babyBearModulus where
  rows := [addRow, hintRow, readRow]
  rom := ROM.table cells seed
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 12 (16, 0)
  initialMemory := seed
  terminalMemory := [regToken 0 14 0 0, regToken 1 8 0x5678 0x1234,
    regToken 2 10 0x5679 0x1234] ++ seed.drop 3

private theorem zero_registers : ∀ index, (Cell.register index).read before = .ok 0 before := by
  have numeric : ∀ index : Nat, index < 32 →
      (Cell.register (BitVec.ofNat 5 index)).read before = .ok 0 before := by
    intro index bound
    interval_cases index
    all_goals first
      | rfl
      | (apply read_register; simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert])
  intro index
  simpa using numeric index.toNat index.isLt

private theorem image : initialImage before cells = some seed := by
  simp only [initialImage, cells, Tests.TraceExecution.cells, List.mapM_cons,
    List.mapM_nil, zero_registers, bind, Option.bind]
  rfl

private theorem configuration : Configured before := by
  have written : run (SailRV32.Functions.wX_bits (.Regidx 1) 0)
      Tests.TraceExecution.before = .ok ()
        { Tests.TraceExecution.before with regs := Tests.TraceExecution.before.regs.insert .x1 0 } := by
    simp only [SailRV32.Functions.wX_bits, SailRV32.Functions.wX,
      SailRV32.Functions.regval_into_reg, write_callback_pure]
    exact run_bind_of_ok _ _ _ _ _ (write_register .x1 0 Tests.TraceExecution.before)
  have preserved := configuration_gpr_write Tests.TraceExecution.configuration 1 0 written
  exact configuration_register_frame
    (before := { Tests.TraceExecution.before with
      regs := Tests.TraceExecution.before.regs.insert .x1 (0 : BitVec 32) })
    (after := before) rfl preserved

private theorem bytes (entry : ProgramEntry) (member : entry ∈ program) :
    (Cell.ram entry.pc).read before = .ok entry.bits before := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [Cell.read, readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, EStateM.pure, before,
    readEntry, addEntry, hintEntry, Std.ExtHashMap.getElem_insert]

private theorem decoding (entry : ProgramEntry) (member : entry ∈ program) :
    Airbender.Reference.RiscV.Sail.decodeOnReset entry.bits = some entry.instruction := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals dsimp only [readEntry, addEntry, hintEntry]
  all_goals decode_on_reset

private theorem public_image : programImageWith NonDeterminism.decoderFields before [0, 4, 8] =
    some program := by
  have read := bytes readEntry (by simp [program])
  have add := bytes addEntry (by simp [program])
  have hint := bytes hintEntry (by simp [program])
  have decodeRead := decoding readEntry (by simp [program])
  have decodeAdd := decoding addEntry (by simp [program])
  have decodeHint := decoding hintEntry (by simp [program])
  simp only [readEntry, addEntry, hintEntry] at read add hint decodeRead decodeAdd decodeHint
  simp only [programImageWith, List.mapM_cons, List.mapM_nil, programEntryWith,
    read, add, hint, decodeRead, decodeAdd, decodeHint, bind, Option.bind]
  rfl

private theorem inputs : NativeBootBoundary trace before cells program NonDeterminism.decoderFields := by
  refine {
    registers := Tests.TraceExecution.inputs.registers
    distinct := by decide
    aligned := Tests.TraceExecution.inputs.aligned
    ordinary := Tests.TraceExecution.inputs.ordinary
    configuration := configuration
    programImage := ⟨[0, 4, 8], public_image⟩
    code := ?_
    profile := ⟨?_, zero_registers, ?_⟩
    seed := rfl
    initial := rfl
    rom := ⟨seed, image, rfl⟩ }
  · intro entry member
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide
  · apply read_register
    simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  · intro address member _
    simp [cells, Tests.TraceExecution.cells] at member

private theorem native_constraints (row : Row babyBearModulus) (member : row ∈ trace.rows) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom) := by
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [Row.constraints, readRow, addRow, hintRow,
    AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, readAssignment, addAssignment, hintAssignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, readAssignment, addAssignment,
         hintAssignment, limbBase, ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, readAssignment, addAssignment,
         hintAssignment, timestampBase, ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])

private theorem accepted : Accepted trace := by
  refine ⟨native_constraints, ?_, ?_, ?_⟩
  · intro row member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · change [trace.initial, addRow.finish, hintRow.finish, readRow.finish].Perm
      [hintRow.finish, readRow.finish, addRow.finish, trace.initial]
    exact (List.reverse_perm [trace.initial, addRow.finish, hintRow.finish, readRow.finish]).symm.trans
      (List.Perm.swap _ _ _)
  · decide

private theorem decoded : Decoded trace program := by
  intro row member
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals change ∃ i : Fin 3, _
  · exact ⟨1, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨0, by decide⟩

private theorem ports : NonDeterminism.StreamPorts trace [0x12345678, 0xbeef] := by
  intro row member read
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases read
  · cases read
  · decide

/-- One native read followed by dependent arithmetic and a hint: native clocks
    supply the order, the real Sail x2 value is derived, and the counter is one. -/
theorem complete_mixed_trace  :
    ∃ after, NonDeterminism.ExecutionTrace [0x12345678, 0xbeef] program (before, 0) (after, 1) ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 12 after ∧
      (Cell.register 2).read after = .ok 0x12345679 after := by
  obtain ⟨after, execution, pc, terminal⟩ := NonDeterminism.native_boot_soundness inputs accepted decoded ports
  refine ⟨after, execution, pc, ?_⟩
  have read := terminal (regToken 2 10 0x5679 0x1234) (by simp [trace])
  obtain ⟨cell, _, equal, actual⟩ := read
  have same : cell = .register 2 := Proofs.cell_address_injective equal
  subst cell
  simpa [regToken, ROMView.token, ROMView.shadow, Cell.addressCode, memoryWord,
    Nat.unpair_pair, Word.toBitVec, Word.value, limbBase] using actual

theorem short_stream_rejected : ¬ NonDeterminism.StreamPorts trace [] := by
  intro supplied
  have read := supplied readRow (by simp [trace]) (by decide)
  cases read

theorem wrong_response_rejected : ¬ NonDeterminism.StreamPorts trace [0xbeef] := by
  intro supplied
  have read := supplied readRow (by simp [trace]) (by decide)
  have impossible : (0xbeef : BitVec 32) = 0x12345678 := Option.some.inj read
  contradiction

end Tests.OracleTrace
