import Slop.Sail.ResetState
import Slop.Trace.PooledOracleConsumption
import Slop.Trace.PooledOracleDecoder
import Slop.Trace.PooledOracleExecution
import Slop.BabyBear
import Tests.ShiftBinopTimestamp
import Tests.TraceExecution

namespace Tests.PooledOracle
open Airbender Arithmetic Trace
open Reference.RiscV.Sail Reference.Sail
open Trace.Proofs _root_.Sail.ArchSem
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def readAssignment (second : Bool) : Nat → ZMod babyBearModulus
  | 0 => if second then 8 else 0
  | 2 => if second then 12 else 4
  | 19 => if second then 12 else 4
  | 21 => if second then 16 else 8
  | 4 | 7 | 18 | 42 | 43 | 44 => 1
  | 23 => if second then 9 else 0
  | 27 => if second then 12 else 4
  | 35 => if second then 10 else 0
  | 33 => if second then 0xbeef else 0x5678
  | 34 => if second then 0 else 0x1234
  | _ => 0

private def shiftAssignment : Nat → ZMod babyBearModulus
  | 0 => 4
  | 2 | 13 | 23 => 8
  | 15 => 12
  | 17 => 5
  | 29 => 0x5678
  | 30 => 0x1234
  | 33 => 6
  | i => if i = 14 then 0 else Tests.ShiftBinopTimestamp.assignment false i

private def readRow (second : Bool) : Row babyBearModulus PooledFamily :=
  ⟨.addSub, readAssignment second⟩
private def shiftRow : Row babyBearModulus PooledFamily := ⟨.shiftBinop, shiftAssignment⟩
private def token (index time lo hi : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (time, 0), Nat.pair lo hi⟩
private def cells := Tests.TraceExecution.cells
private def seed : List (MemoryToken babyBearModulus) :=
  (List.range 32).map fun index => token index 0 0 0

private noncomputable def before : State :=
  { Tests.TraceExecution.before with
    regs := Tests.TraceExecution.before.regs.insert .x1 0
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 0 (0xF3 : BitVec 8)
      |>.insert 1 0x10 |>.insert 2 0 |>.insert 3 0x7C
      |>.insert 4 0xB3 |>.insert 5 0x40 |>.insert 6 0 |>.insert 7 0
      |>.insert 8 0xF3 |>.insert 9 0x10 |>.insert 10 0 |>.insert 11 0x7C }

private theorem configuration : Configured before :=
  (Tests.TraceExecution.configuration.insert (key := .x1) rfl 0).with_mem _


-- Read x1, XOR x1,x0,x0, then read x1 again. Physical row order is scrambled.
private noncomputable def trace : PooledTrace babyBearModulus where
  rows := [shiftRow, readRow true, readRow false]
  rom := ⟨ROM.table cells seed, Verification.subwordTable (ROM.words before)⟩
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 12 (16, 0)
  initialMemory := seed
  terminalMemory := [token 0 13 0 0, token 1 14 0xbeef 0] ++ seed.drop 2

private theorem read_constraints (second : Bool) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (readAssignment second)) AddSub.clockConstraints := by
  cases second <;>
    simp [AddSub.clockConstraints, AddSub.importedConstraints,
      AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, Verification.environment, readAssignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, readAssignment,
         limbBase, ZMod.val_ofNat, babyBearModulus])
    | (apply Trace.Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, readAssignment,
         timestampBase, ZMod.val_ofNat, babyBearModulus])

private theorem shift_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment shiftAssignment) ShiftBinop.clockConstraints := by
  apply Verification.holds_append (left := ShiftBinop.importedConstraints)
    (right := ShiftBinop.importedConstraintsTimestampLookups)
  · have core := Tests.ShiftBinop.satisfies
    simp [ShiftBinop.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Lookup.Contains, Vector.map, Expression.eval, Verification.environment, shiftAssignment,
      Tests.ShiftBinopTimestamp.assignment, Tests.ShiftBinop.row,
      Verification.range16, Verification.shiftBinopLookup,
      show (4 : ZMod babyBearModulus) + 4 + -8 = 0 by decide,
      show (8 : ZMod babyBearModulus) + 4 + -12 = 0 by decide] at core ⊢
    refine ⟨?_, ?_, core.2.2.2.2⟩
    · have bound := Verification.range16_contains
        (entry := Expression.const (8 : ZMod babyBearModulus))
        (env := Verification.environment shiftAssignment) (by decide)
      simpa [Verification.range16, Lookup.Contains, Vector.map, Expression.eval,
        Verification.environment] using bound
    · have bound := Verification.range16_contains
        (entry := Expression.const (0 : ZMod babyBearModulus))
        (env := Verification.environment shiftAssignment) (by decide)
      simpa [Verification.range16, Lookup.Contains, Vector.map, Expression.eval,
        Verification.environment] using bound
  · simp [ShiftBinop.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
    repeat' apply And.intro
    all_goals apply Trace.Proofs.range_contains
    all_goals simp [Expression.eval, Verification.environment, shiftAssignment,
      Tests.ShiftBinopTimestamp.assignment]
    all_goals decide

private theorem accepted : Accepted trace := by
  constructor
  · intro row member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact shift_constraints
    · exact read_constraints true
    · exact read_constraints false
  · intro row member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · change [trace.initial, shiftRow.finish, (readRow true).finish, (readRow false).finish].Perm
      [(readRow true).finish, (readRow false).finish, shiftRow.finish, trace.initial]
    exact (List.reverse_perm [trace.initial, shiftRow.finish, (readRow true).finish,
      (readRow false).finish]).symm.trans (List.Perm.swap _ _ _)
  · decide

private theorem clocks : ClockBoundary trace := by
  constructor
  · constructor <;> decide
  · decide
  · intro seed member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    change 0 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide

private theorem ports : NonDeterminism.Pooled.StreamPorts trace [0x12345678, 0xbeef, 0xcafe] := by
  intro row member selected
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases selected
  · decide
  · decide

theorem mixed_native_consumption :
    ∃ rows, rows.Perm trace.rows ∧
      rows.Pairwise (fun a b => b.clock < a.clock) ∧
      ∃ rest, [0x12345678, 0xbeef, 0xcafe] = NonDeterminism.Pooled.consumed rows ++ rest :=
  NonDeterminism.Pooled.Proofs.native_consumption (by decide) (by decide) accepted clocks ports

theorem chronological_response_order :
    NonDeterminism.Pooled.consumed [readRow true, shiftRow, readRow false] = [0x12345678, 0xbeef] ∧
      NonDeterminism.Pooled.readIndex trace (readRow false) = 0 ∧
      NonDeterminism.Pooled.readIndex trace (readRow true) = 1 ∧ NonDeterminism.Pooled.readCount trace = 2 := by
  decide

theorem wrong_stream_order_rejected : ¬ NonDeterminism.Pooled.StreamPorts trace [0xbeef, 0x12345678] := by
  intro supplied
  have mismatch := supplied (readRow false) (by simp [trace]) (by decide)
  have impossible : (0xbeef : BitVec 32) = 0x12345678 := Option.some.inj mismatch
  contradiction

theorem short_stream_rejected : ¬ NonDeterminism.Pooled.StreamPorts trace [0x12345678] := by
  intro supplied
  have missing := supplied (readRow true) (by simp [trace]) (by decide)
  cases missing

theorem foreign_selector_ignored (family : PooledFamily) (other : family ≠ .addSub) :
    NonDeterminism.Pooled.isRead (⟨family, fun _ => 1⟩ : Row babyBearModulus PooledFamily) = false := by
  cases family <;> simp_all [NonDeterminism.Pooled.isRead]


private noncomputable def readEntry (second : Bool) : PooledProgramEntry :=
  ⟨if second then 8 else 0, 0x7C0010F3, .CSRReg (0x7C0, .Regidx 0, .Regidx 1, .CSRRW),
    ⟨.addSub, 0, 0, 1, ⟨0, 0⟩, 256, 0⟩⟩
private def shiftEntry : PooledProgramEntry :=
  ⟨4, 0x000040B3, .RTYPE (.Regidx 0, .Regidx 0, .Regidx 1, .XOR),
    ⟨.shiftBinop, 0, 0, 1, ⟨0, 0⟩, 2, 4⟩⟩
private noncomputable def program := [readEntry false, shiftEntry, readEntry true]

private theorem loads : NoDiscardedLoads program := by
  intro entry member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> intros <;> simp [readEntry, shiftEntry]

private theorem bytes (entry : PooledProgramEntry) (member : entry ∈ program) :
    (Cell.ram entry.pc).read before = .ok entry.bits before := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
    get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
    before, readEntry, shiftEntry, Std.ExtHashMap.getElem_insert]

private theorem decoding (entry : PooledProgramEntry) (member : entry ∈ program) :
    Airbender.Reference.RiscV.Sail.decodeOnReset entry.bits = some entry.instruction := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals
    dsimp only [readEntry, shiftEntry]
    decode_on_reset

private theorem fields (entry : PooledProgramEntry) (member : entry ∈ program) :
    NonDeterminism.Pooled.decoderFields entry.instruction = some entry.data := by
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem actual_public_image : NonDeterminism.Pooled.programImage before [0, 4, 8] =
    some program := by
  have first := bytes (readEntry false) (by simp [program])
  have shift := bytes shiftEntry (by simp [program])
  have second := bytes (readEntry true) (by simp [program])
  have firstDecode := decoding (readEntry false) (by simp [program])
  have shiftDecode := decoding shiftEntry (by simp [program])
  have firstFields := fields (readEntry false) (by simp [program])
  have shiftFields := fields shiftEntry (by simp [program])
  simp only [readEntry, shiftEntry, Bool.false_eq_true, ↓reduceIte] at first shift second firstDecode shiftDecode firstFields shiftFields
  simp only [NonDeterminism.Pooled.programImage, programImageWith,
    List.mapM_cons, List.mapM_nil, programEntryWith, first, shift, second,
    firstDecode, shiftDecode, firstFields, shiftFields,
    bind, Option.bind, pure]
  rfl

private theorem decoded : PooledDecoded trace program := by
  intro row member
  simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · change ∃ i : Fin 1, _
    exact ⟨0, by decide⟩
  · change ∃ i : Fin 2, _
    exact ⟨1, by decide⟩
  · change ∃ i : Fin 2, _
    exact ⟨0, by decide⟩

theorem actual_read_classification : ∀ row ∈ trace.rows,
    NonDeterminism.Pooled.Fetched row before :=
  NonDeterminism.Pooled.Proofs.decoder_soundness (by decide) accepted actual_public_image decoded

theorem malformed_csr_rejected :
    NonDeterminism.Pooled.decoderFields (.CSRReg (0x7C0, .Regidx 0, .Regidx 0, .CSRRW)) = none ∧
    NonDeterminism.Pooled.decoderFields (.CSRReg (0x7C0, .Regidx 1, .Regidx 1, .CSRRW)) = none ∧
    NonDeterminism.Pooled.decoderFields (.CSRReg (0x7C1, .Regidx 0, .Regidx 1, .CSRRW)) = none := by
  decide

private def wrongReadRow : Row babyBearModulus PooledFamily :=
  ⟨.addSub, fun i => if i = 18 then 0 else readAssignment false i⟩

theorem wrong_read_selector_rejected :
    ¬ PooledDecoded { trace with rows := [wrongReadRow] } program := by
  intro admitted
  have queried := admitted wrongReadRow (by simp)
  have mismatch : ¬ (decoderTable program .addSub).Contains #[] wrongReadRow.decoderQuery := by
    change ¬ ∃ i : Fin 2, _
    decide
  exact mismatch queried

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

private theorem image : initialImage before cells = some trace.initialMemory := by
  simp only [initialImage, cells, Tests.TraceExecution.cells, List.mapM_cons, List.mapM_nil, zero_registers]
  rfl

theorem mixed_initialized_history : ∃ after : State,
    (Cell.register 1).read after = .ok 0xbeef after := by
  obtain ⟨history, _, after, consistent, _, _, _, matched⟩ :=
    Trace.Proofs.pooled_native_history (by decide) (by decide) accepted clocks
      image (by decide) (by simp [cells, Tests.TraceExecution.cells, Cell.Aligned]) actual_public_image decoded
  obtain ⟨cell, _, same, read⟩ := Trace.Proofs.terminal_sail_reads
    (by decide) (by decide) accepted clocks image (by decide) consistent matched
      (token 1 14 0xbeef 0) (by simp [trace])
  have code : cell.addressCode = (Cell.register 1).addressCode := same
  have eq := Trace.Proofs.cell_address_injective code
  subst cell
  have value : Trace.memoryWord (token 1 14 0xbeef 0).value = 0xbeef := by
    simp only [Trace.memoryWord, token, Nat.unpair_pair]
    rfl
  rw [value] at read
  exact ⟨after, read⟩

theorem mixed_history_bounds :
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded) ∧
    (∀ row ∈ trace.rows, ∀ port ∈ row.ports,
      (writeToken row.columns row.assignment port).word.Bounded) ∧
    (∀ sink ∈ trace.terminalMemory, sink.word.Bounded) :=
  Trace.Proofs.pooled_value_bounds (by decide) (by decide) accepted clocks image
    rfl (values := ROM.words before) rfl actual_public_image decoded

private def wrongSourceRow : Row babyBearModulus PooledFamily :=
  ⟨.shiftBinop, fun i => if i = 29 then 0 else shiftAssignment i⟩

theorem fabricated_read_rejected :
    ¬ Accepted { trace with rows := [wrongSourceRow, readRow true, readRow false] } := by
  intro admitted
  have mismatch : ¬ (trace.initialMemory ++
      [wrongSourceRow, readRow true, readRow false].flatMap Row.writes).Perm
      (trace.terminalMemory ++ [wrongSourceRow, readRow true, readRow false].flatMap Row.reads) := by
    decide
  exact mismatch admitted.memory

theorem external_read_retirement  (second : Bool) :
    ∃ rowBefore rowAfter original,
      NonDeterminism.clause [0x12345678, 0xbeef, 0xcafe]
        (NonDeterminism.Pooled.readIndex trace (readRow second))
        (readEntry second).instruction .sail = some
          (original, NonDeterminism.Pooled.readIndex trace (readRow second) + 1) ∧
      run (normalStep original) (retiredState rowBefore (readRow second).start.word.toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState rowAfter (readRow second).finish.word.toBitVec) := by
  have member : readRow second ∈ trace.rows := by cases second <;> simp [trace]
  obtain ⟨_, rows, nativeAfter, _, permutation, _, nativeHistory, _⟩ :=
    Trace.Proofs.pooled_native_history (by decide) (by decide) accepted clocks
      image (by decide) (by simp [cells, Tests.TraceExecution.cells, Cell.Aligned]) actual_public_image decoded
  obtain ⟨front, back, same⟩ := List.mem_iff_append.mp (permutation.mem_iff.mpr member)
  have grouped : Trace.SailHistory cells
      ((front.flatMap fun row => (Trace.rowEvents trace.memoryEpoch row).reverse) ++
        (Trace.rowEvents trace.memoryEpoch (readRow second)).reverse ++
        (back.flatMap fun row => (Trace.rowEvents trace.memoryEpoch row).reverse)) before nativeAfter := by
    simpa only [same, List.flatMap_append, List.flatMap_cons, List.append_assoc] using nativeHistory
  rw [List.append_assoc] at grouped
  obtain ⟨rowAfter, throughRow, _⟩ := Trace.Proofs.sail_history_append.mp grouped
  obtain ⟨rowBefore, past, current⟩ := Trace.Proofs.sail_history_append.mp throughRow
  have registers : ∀ index, Cell.register index ∈ cells := by
    have numeric : ∀ index : Nat, index < 32 → Cell.register (BitVec.ofNat 5 index) ∈ cells := by
      intro index bound
      interval_cases index <;> decide
    intro index
    simpa using numeric index.toNat index.isLt
  have query : (readRow second).decoderQuery = (readEntry second).query := by
    cases second <;> decide
  obtain ⟨original, selected, executed⟩ := NonDeterminism.Pooled.Proofs.addsub_execution
    (by decide) (by decide) accepted clocks image rfl (values := ROM.words before) rfl
    registers actual_public_image decoded loads
    member (by cases second <;> simp [program]) rfl query
    (ports (readRow second) member) past current
  cases second <;> exact ⟨rowBefore, rowAfter, original, selected, executed⟩

private theorem inputs : PooledBootInputs trace before cells program NonDeterminism.Pooled.decoderFields := by
  refine {
    registers := Tests.TraceExecution.inputs.registers
    ordinary := Tests.TraceExecution.inputs.ordinary
    configuration := configuration
    code := ?_
    loads := loads
    distinct := by decide
    aligned := Tests.TraceExecution.inputs.aligned
    programImage := ⟨[0, 4, 8], actual_public_image⟩
    profile := ⟨?_, zero_registers, ?_⟩
    seed := rfl
    initialBoundary := rfl
    physicalImage := ⟨seed, image, rfl⟩
    subwordSetup := rfl
    terminalPC := by constructor <;> decide }
  · intro entry member
    simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide
  · apply read_register
    simp [before, Tests.TraceExecution.before, Std.ExtDHashMap.get?_insert]
  · intro address member _
    simp [cells, Tests.TraceExecution.cells] at member

theorem complete_mixed_trace  :
    ∃ after, NonDeterminism.Pooled.ExecutionTrace [0x12345678, 0xbeef, 0xcafe] program
      (before, 0) (after, 2) ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 12 after ∧
      (Cell.register 1).read after = .ok 0xbeef after := by
  obtain ⟨after, execution, pc, terminal⟩ :=
    NonDeterminism.Pooled.native_soundness inputs accepted decoded ports
  obtain ⟨cell, _, address, read⟩ := terminal (token 1 14 0xbeef 0) (by simp [trace])
  have same : cell = .register 1 := cell_address_injective address
  subst cell
  have value : (ROMView.token before (token 1 14 0xbeef 0)).word.toBitVec = 0xbeef := by
    simp only [ROMView.token, ROMView.shadow, token, Cell.addressCode, Nat.unpair_pair,
      Nat.reduceEqDiff, false_and, ite_false, MemoryToken.word]
    rfl
  rw [value] at read
  exact ⟨after, execution, pc, read⟩

end Tests.PooledOracle
