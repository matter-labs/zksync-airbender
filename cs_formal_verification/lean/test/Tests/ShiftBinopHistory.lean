import Tests.ShiftBinopTimestamp
import Slop.ShiftBinop.Trace
import Slop.ShiftBinop.Values
import Slop.ShiftBinop.PortReads
import Slop.ShiftBinop.Execution
import Slop.ShiftBinop.Claims
import Slop.Sail.WordMemoryState

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
      SailHistory cells
        (rows.flatMap fun row => (Trace.rowEvents (trace rom).memoryEpoch row).reverse) before after ∧
      SailStateMatches cells history after := by
  apply Airbender.ShiftBinop.Proofs.decoded_native_history (by decide) (by decide)
    (accepted rom) (boundary rom) image (by decide) _ program_image (decoded rom)
  intro cell member
  simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> trivial

theorem actual_native_bounds (rom : Table (ZMod babyBearModulus) (fields 9)) :
    (∀ actual ∈ (trace rom).rows, ∀ port ∈ actual.ports,
      (readToken actual.assignment port).word.Bounded) ∧
    (∀ actual ∈ (trace rom).rows, ∀ port ∈ actual.ports,
      (writeToken actual.columns actual.assignment port).word.Bounded) ∧
    (∀ token ∈ (trace rom).terminalMemory, token.word.Bounded) :=
  Airbender.ShiftBinop.Proofs.native_value_bounds (by decide) (by decide)
    (accepted rom) (boundary rom) image program_image (decoded rom)

theorem actual_zero_tokens (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∀ actual ∈ (trace rom).rows, ∀ port ∈ actual.ports,
      port.address.code actual.assignment = (Cell.register 0).addressCode →
      (readToken actual.assignment port).value = 0 :=
  Airbender.ShiftBinop.Proofs.native_zero_reads (by decide) (by decide)
    (accepted rom) (boundary rom) image program_image (decoded rom)

/-- The accepted aliased byte-port history supplies the actual Sail reads
    and destination write, before adding instruction execution/retirement. -/
theorem actual_register_transport (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after,
      run (SailRV32.Functions.rX_bits (.Regidx 0)) before = .ok 0 before ∧
      run (SailRV32.Functions.wX_bits (.Regidx 1) 0) before = .ok () after := by
  obtain ⟨_, rows, after, _, permutation, _, native, _⟩ := actual_native_history rom
  have single : rows = [row] := List.perm_singleton.mp permutation
  rw [single] at native
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at native
  have query : Airbender.ShiftBinop.decoderQuery row.assignment = entry.query := by decide
  have read := Airbender.ShiftBinop.Proofs.register_reads (by decide) (trace rom).memoryEpoch
    query native 0
  have write := Airbender.ShiftBinop.Proofs.register_write (by decide) (trace rom).memoryEpoch
    query native
  refine ⟨after, ?_, ?_⟩
  · simpa [entry, row, Tests.ShiftBinopTimestamp.assignment, Tests.ShiftBinop.row,
      Airbender.ShiftBinop.importedConstraintsMemoryPorts, MemoryPort.readCode,
      Trace.memoryWord, WordColumns.code, WordColumns.evaluate, Word.toBitVec,
      Word.value, Nat.unpair_pair] using read
  · simpa [entry, row, Tests.ShiftBinopTimestamp.assignment, Tests.ShiftBinop.row,
      Airbender.ShiftBinop.importedConstraintsMemoryPorts, MemoryPort.writeCode,
      Trace.memoryWord, WordColumns.code, WordColumns.evaluate, Word.toBitVec,
      Word.value, Nat.unpair_pair] using write

/-- Actual imported acceptance, public decoding and grouped history feed the
    native row theorem through original Sail execution and retirement. -/
theorem actual_register_retirement (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after,
      run (normalStep (SailRV32.Functions.execute_RTYPE (.Regidx 0) (.Regidx 0) (.Regidx 1) .XOR))
        (retiredState before 65532) = .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after 65536) := by
  obtain ⟨_, rows, after, _, permutation, _, native, _⟩ := actual_native_history rom
  have single : rows = [row] := List.perm_singleton.mp permutation
  rw [single] at native
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at native
  have query : Airbender.ShiftBinop.decoderQuery row.assignment = entry.query := by decide
  have checked := Airbender.ShiftBinop.Proofs.row_execution (by decide) (by decide)
    (by decide) (accepted rom) (boundary rom) image program_image (decoded rom)
    (by simp [trace]) (by simp) query .xor false 0 0 0 1 rfl native
  refine ⟨after, ?_⟩
  simpa [entry, row, Tests.ShiftBinopTimestamp.assignment, Tests.ShiftBinop.row,
    Airbender.ShiftBinop.execution, Airbender.ShiftBinop.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, Airbender.ShiftBinop.importedConstraintsMemoryPorts,
    MemoryPort.readCode, memoryWord, WordColumns.code, WordColumns.evaluate,
    Word.toBitVec, Word.value, Nat.unpair_pair, limbBase,
    show (65532 : ZMod babyBearModulus).val = 65532 by decide,
    show (1 : ZMod babyBearModulus).val = 1 by decide] using checked


/-- Public fetch/decoding and native histories compose from the unchanged
    public state through original Sail execution to the terminal PC. -/
theorem actual_register_trace [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
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

private def pooledProgram : List PooledProgramEntry :=
  [entry.mapFamily (fun _ => .shiftBinop)]

private def pooled : PooledTrace babyBearModulus where
  rows := [⟨.shiftBinop, row.assignment⟩]
  rom := ⟨ROM.table cells seed, Verification.subwordTable (ROM.words before)⟩
  initial := (trace (ROM.table cells seed)).initial
  terminal := (trace (ROM.table cells seed)).terminal
  initialMemory := seed
  terminalMemory := (trace (ROM.table cells seed)).terminalMemory

private theorem pooledAccepted : Accepted pooled := by
  constructor
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    exact Tests.ShiftBinopTimestamp.constraints false
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    rfl
  · exact (accepted (ROM.table cells seed)).states
  · exact (accepted (ROM.table cells seed)).memory

private theorem pooledImage : pooledProgramImage before [65532] = some pooledProgram := by
  have source := Proofs.run_program_sources program_image entry (by simp)
  have bytes := source.bytes
  change (Cell.ram 65532).read before = .ok entry.bits before at bytes
  simp only [pooledProgramImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, source.decoded, bind, Option.bind]
  rfl

private theorem pooledDecoded : PooledDecoded pooled pooledProgram := by
  intro actual member
  simp only [pooled, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _ = _
  exact ⟨0, by decide⟩

private theorem pooledInputs : NativeInputs pooledDecoderFields pooled before cells pooledProgram := by
  refine ⟨by decide, ?_, image, ?_, ⟨[65532], pooledImage⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  · refine ⟨(4, 0), ?_⟩
    have read : run (SailRV32.Functions.get_arch_pc ()) before = .ok 65532 before := by
      apply read_register
      simp [before, wordWriteState]
    rw [initialState, read]
    rfl
  · exact ⟨(boundary (ROM.table cells seed)).initial,
      (boundary (ROM.table cells seed)).aligned, (boundary (ROM.table cells seed)).memory⟩

/-- The per-circuit XOR claim is inhabited by actual public decoding and an
    accepted aliased byte-port history, with no assumed ranges or reads. -/
theorem per_circuit_xor_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] :
    ∃ input : Airbender.ShiftBinop.Input,
      (Airbender.ShiftBinop.circuitModel pooled before cells pooledProgram).relation
        input ⟨⟨0, 0⟩, ⟨0, 1⟩⟩ row.assignment ∧
      Airbender.ShiftBinop.InterfaceAssumptions pooled before cells pooledProgram ∧
      Airbender.ShiftBinop.spec input ⟨⟨0, 0⟩, ⟨0, 1⟩⟩ := by
  have member : (⟨.shiftBinop, row.assignment⟩ : Row babyBearModulus PooledFamily) ∈ pooled.rows :=
    by simp [pooled]
  obtain ⟨current, position⟩ := Proofs.pooled_row_position_exists (by decide) (by decide)
    pooledAccepted pooledInputs.clocks pooledInputs.image pooledInputs.distinct pooledInputs.aligned
    pooledImage pooledDecoded member
  let input : Airbender.ShiftBinop.Input :=
    ⟨.xor, false, 0, 0, ⟨65532, 0⟩, .Regidx 0, .Regidx 0, .Regidx 1, 0, current⟩
  let output : Output := ⟨⟨0, 0⟩, ⟨0, 1⟩⟩
  have mapping : Airbender.ShiftBinop.TraceMapping pooled before cells pooledProgram
      input output row.assignment := by
    refine ⟨?_, position, ?_⟩
    · constructor
      · intro i; dsimp only [input]; fin_cases i <;> decide
      · intro _ i; dsimp only [input]; fin_cases i <;> decide
      · intro impossible; contradiction
      · intro impossible; contradiction
      all_goals rfl
    · exact ⟨entry.mapFamily (fun _ => .shiftBinop), by simp [pooledProgram], rfl, by decide, rfl⟩
  have assumptions : Airbender.ShiftBinop.InterfaceAssumptions pooled before cells pooledProgram := ⟨pooledInputs⟩
  have core := Verification.holds_of_sublist (Tests.ShiftBinopTimestamp.constraints false)
    (List.sublist_append_left Airbender.ShiftBinop.importedConstraints
      Airbender.ShiftBinop.importedConstraintsTimestampLookups)
  have relation : (Airbender.ShiftBinop.circuitModel pooled before cells pooledProgram).relation
      input output row.assignment := ⟨⟨pooledAccepted, pooledDecoded, member⟩, mapping⟩
  exact ⟨input, relation, assumptions, Airbender.ShiftBinop.babyBear_soundness pooled before
    cells pooledProgram assumptions input output _ relation⟩

/-- Canonical PC mapping rejects a field alias after local range assumptions are removed. -/
theorem per_circuit_pc_alias_rejected [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (current : State) :
    ¬ Airbender.ShiftBinop.TraceMapping pooled before cells pooledProgram
      (⟨.xor, false, 0, 0, ⟨babyBearModulus + 65532, 0⟩,
        .Regidx 0, .Regidx 0, .Regidx 1, 0, current⟩ : Airbender.ShiftBinop.Input)
      ⟨⟨0, 0⟩, ⟨0, 1⟩⟩ row.assignment := by
  intro mapping
  have impossible := mapping.words.pcLo
  change babyBearModulus + 65532 = (row.assignment 0).val at impossible
  have small := ZMod.val_lt (row.assignment 0)
  omega

end Tests.ShiftBinopHistory
