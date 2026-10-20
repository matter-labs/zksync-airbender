import Tests.MulDivDecoder
import Slop.MulDiv.Execution
import Slop.Sail.DecoderFrame
import Slop.MulDiv.Claims

namespace Tests.MulDivTrace
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

private def entry (remainder : Bool) : Airbender.MulDiv.ProgramEntry :=
  ⟨0x3fffc, if remainder then 0x0220f0b3 else 0x0220d0b3,
    if remainder then .REM (.Regidx 2, .Regidx 1, .Regidx 1, true)
    else .DIV (.Regidx 2, .Regidx 1, .Regidx 1, true),
    ⟨(), 1, 2, 1, ⟨0, 0⟩, if remainder then 8 else 4, 0⟩⟩

private def initial : State :=
  { (default : State) with regs :=
    (((Std.ExtDHashMap.emptyWithCapacity.insert .x1 (0x20007 : BitVec 32)).insert
      .x2 (0 : BitVec 32)).insert .PC (0x3fffc : BitVec 32)).insert .misa (0x40001000 : BitVec 32) }

private def before (remainder : Bool) : State := wordWriteState initial 0x3fffc (entry remainder).bits
private def cells : List Cell := [.register 0, .register 1, .register 2]
private def seed : List (MemoryToken babyBearModulus) :=
  [Cell.initialToken (.register 0) 0, Cell.initialToken (.register 1) 0x20007,
    Cell.initialToken (.register 2) 0]
private def row (remainder : Bool) : Row babyBearModulus Airbender.MulDiv.TraceKind :=
  ⟨.mulDiv, Tests.MulDivTimestamp.assignment remainder false⟩

private def token (index clock value : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (clock, 0), value⟩

private def trace (remainder : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Airbender.MulDiv.NativeTrace babyBearModulus where
  rows := [row remainder]
  rom := rom
  initial := (row remainder).start
  terminal := (row remainder).finish
  initialMemory := seed
  terminalMemory := [token 0 0 0,
    token 1 6 (if remainder then Nat.pair 7 2 else Nat.pair 65535 65535), token 2 5 0]

private theorem accepted (remainder : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Accepted (trace remainder rom) := by
  constructor
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    exact Tests.MulDivTimestamp.constraints remainder false
  · intro actual member
    simp only [trace, List.mem_singleton] at member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · cases remainder <;>
      dsimp [trace, Row.reads, Row.writes, Row.ports, Row.columns, row,
        Airbender.MulDiv.importedConstraintsMemoryPorts, Airbender.MulDiv.importedConstraintsTraceColumns]
    all_goals decide

private theorem boundary (remainder : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ClockBoundary (trace remainder rom) := by
  constructor
  · change 4 < timestampBase ∧ 0 < timestampBase
    constructor <;> decide
  · change 4 % 4 = 0
    decide
  · intro actual member
    simp only [trace, seed, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

private theorem image (remainder : Bool) : initialImage (before remainder) cells = some seed := by
  have zero : (Cell.register 0).read (before remainder) = .ok 0 (before remainder) := rfl
  have one : (Cell.register 1).read (before remainder) = .ok 0x20007 (before remainder) := by
    apply read_register
    simp [before, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  have two : (Cell.register 2).read (before remainder) = .ok 0 (before remainder) := by
    apply read_register
    simp [before, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
  simp only [initialImage, cells, seed, List.mapM_cons, List.mapM_nil, zero, one, two]
  rfl

private theorem program_image (remainder : Bool) :
    Airbender.MulDiv.programImage (before remainder) [0x3fffc] = some [entry remainder] := by
  have bytes : (Cell.ram 0x3fffc).read (before remainder) =
      .ok (entry remainder).bits (before remainder) := written_word_read _ 0x3fffc _
  have isa : run (SailRV32.readReg .misa) (before remainder) =
      .ok (0x40001000 : BitVec 32) (before remainder) := by
    apply read_register
    simp [before, initial, wordWriteState]
  have decoded : run (SailRV32.Functions.encdec_backwards (entry remainder).bits) (before remainder) =
      .ok (entry remainder).instruction (before remainder) := by
    cases remainder
    all_goals
      repeat' first
        | (with_unfolding_all rfl)
        | (with_unfolding_all conv_lhs => arg 1; whnf
           rw [@run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
             _ _ SailRV32.Register.misa _ _ _ isa])
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, bind, Option.bind]
  cases remainder <;> rfl

/-- The real public DIVU/REMU encoding decodes identically after GPR, PC,
    nextPC and memory changes; only the public ISA configuration is retained. -/
theorem decoder_configuration_frame (remainder : Bool) (pc : BitVec 32) :
    let changed : State := { before remainder with
      regs := (((before remainder).regs.insert .x1 (42 : BitVec 32)).insert .PC pc).insert .nextPC 9
      mem := (default : State).mem }
    run (SailRV32.Functions.encdec_backwards (entry remainder).bits) changed =
      .ok (entry remainder).instruction changed := by
  have source := Proofs.run_program_sources (program_image remainder)
    (entry remainder) (by simp)
  apply (decoded_misa_frame _ source.decoded).2
  simp [Std.ExtDHashMap.get?_insert]

private theorem query (remainder : Bool) :
    Airbender.MulDiv.decoderQuery (Tests.MulDivTimestamp.assignment remainder false) =
      (entry remainder).query := by
  cases remainder <;> decide

private theorem decoded (remainder : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    Airbender.MulDiv.Decoded (trace remainder rom) [entry remainder] := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  cases remainder <;> change ∃ i, _
  all_goals exact ⟨⟨0, by decide⟩, query _⟩

/-- Public seed, original M-enabled Sail decoding and native matching derive
    all reads. DIVU/REMU by zero reach the actual aliased rd/rs1 after-state. -/
theorem actual_division_retirement (remainder : Bool)
    (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after,
      run (normalStep (if remainder then
        SailRV32.Functions.execute_REM (.Regidx 2) (.Regidx 1) (.Regidx 1) true
        else SailRV32.Functions.execute_DIV (.Regidx 2) (.Regidx 1) (.Regidx 1) true))
        (retiredState (before remainder) 0x3fffc) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after 0x40000) ∧
      run (SailRV32.Functions.rX_bits (.Regidx 1)) after =
        .ok (if remainder then 0x20007 else 0xffffffff) after := by
  obtain ⟨history, rows, after, _, permutation, _, execution, _⟩ :=
    Airbender.MulDiv.Proofs.decoded_native_history (by decide) (by decide)
      (accepted remainder rom) (boundary remainder rom) (image remainder)
      (by decide)
      (by intro cell member; simp [cells] at member; rcases member with rfl | rfl | rfl <;> trivial)
      (program_image remainder) (decoded remainder rom)
  have single : rows = [row remainder] := by
    simpa only [trace] using List.perm_singleton.mp permutation
  subst rows
  have native : SailHistory cells
      (Airbender.MulDiv.Proofs.nativeEvents (trace remainder rom).memoryEpoch
        (Tests.MulDivTimestamp.assignment remainder false)).reverse (before remainder) after := by
    simpa [Trace.rowEvents, row, Row.ports, Row.columns] using execution
  have checked := Airbender.MulDiv.Proofs.row_rebased_execution (by decide) (by decide) (by decide)
    (accepted remainder rom) (boundary remainder rom) (image remainder)
    (program_image remainder) (decoded remainder rom) (by simp [trace, row]) (by simp) (query remainder)
    (if remainder then .remu else .divu) 1 2 1 (by cases remainder <;> rfl) native
  have written := Airbender.MulDiv.Proofs.register_write (by decide)
    (trace remainder rom).memoryEpoch (query remainder) native
  have code : memoryWord (Airbender.MulDiv.importedConstraintsMemoryPorts[2].writeCode
      (Tests.MulDivTimestamp.assignment remainder false)) =
      (if remainder then 0x20007 else 0xffffffff : BitVec 32) := by
    cases remainder <;>
      norm_num [memoryWord, Airbender.MulDiv.importedConstraintsMemoryPorts,
        MemoryPort.writeCode, pairCode, Tests.MulDivTimestamp.assignment, Tests.MulDiv.row,
        Word.toBitVec, Word.value, ZMod.val_ofNat, babyBearModulus]
    all_goals rfl
  rw [code] at written
  change run (SailRV32.Functions.wX_bits (.Regidx 1) (if remainder then 0x20007 else 0xffffffff))
    (before remainder) = .ok () after at written
  obtain ⟨actual, write, _, read⟩ := gpr_write_readback 1
    (if remainder then 0x20007 else 0xffffffff) (before remainder) (by simp)
  have same := (EStateM.Result.ok.inj (written.symm.trans write)).2
  subst actual
  refine ⟨after, ?_, read⟩
  cases remainder <;>
    norm_num [Airbender.MulDiv.execution, Airbender.MulDiv.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, Tests.MulDivTimestamp.assignment, Tests.MulDiv.row,
      Word.toBitVec, Word.value, limbBase, ZMod.val_ofNat, babyBearModulus] at checked ⊢
  all_goals exact checked

/-- The complete trace starts at the unchanged public state, uses the real
    configuration-dependent decoder and reaches the native terminal PC. -/
theorem actual_division_trace [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (remainder : Bool) (rom : Table (ZMod babyBearModulus) (fields 9)) :
    ∃ after, Airbender.MulDiv.SailTrace [entry remainder] (before remainder) after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok 0x40000 after := by
  have initialPC : initialState (before remainder) (4, 0) = some (trace remainder rom).initial := by
    have read : run (SailRV32.Functions.get_arch_pc ()) (before remainder) =
        .ok 0x3fffc (before remainder) := by
      apply read_register
      simp [before, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
    rw [initialState, read]
    rfl
  have inputs : Airbender.MulDiv.ExecutionBoundary (trace remainder rom)
      (before remainder) cells [entry remainder] := {
    distinct := by decide
    aligned := by intro cell member; simp [cells] at member; rcases member with rfl | rfl | rfl <;> trivial
    image := image remainder
    initialPC := ⟨(4, 0), initialPC⟩
    programImage := ⟨[0x3fffc], program_image remainder⟩
    clocks := boundary remainder rom
  }
  obtain ⟨after, execution, pc, _⟩ := Airbender.MulDiv.trace_soundness
    (by decide) (by decide) (by decide) inputs (accepted remainder rom) (decoded remainder rom)
  exact ⟨after, execution, pc⟩

private def pooledProgram (remainder : Bool) : List PooledProgramEntry :=
  [(entry remainder).mapFamily (fun _ => .mulDiv)]

private def pooled (remainder : Bool) : PooledTrace babyBearModulus where
  rows := [⟨.mulDiv, (row remainder).assignment⟩]
  rom := ⟨ROM.table cells seed, Verification.subwordTable (ROM.words (before remainder))⟩
  initial := (trace remainder (ROM.table cells seed)).initial
  terminal := (trace remainder (ROM.table cells seed)).terminal
  initialMemory := seed
  terminalMemory := (trace remainder (ROM.table cells seed)).terminalMemory

private theorem pooledAccepted (remainder : Bool) : Accepted (pooled remainder) := by
  constructor
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    exact Tests.MulDivTimestamp.constraints remainder false
  · intro actual member
    simp only [pooled, List.mem_singleton] at member
    subst actual
    rfl
  · exact (accepted remainder (ROM.table cells seed)).states
  · exact (accepted remainder (ROM.table cells seed)).memory

private theorem pooledImage (remainder : Bool) :
    pooledProgramImage (before remainder) [0x3fffc] = some (pooledProgram remainder) := by
  have source := Proofs.run_program_sources (program_image remainder) (entry remainder) (by simp)
  have bytes := source.bytes
  change (Cell.ram 0x3fffc).read (before remainder) = .ok (entry remainder).bits (before remainder) at bytes
  simp only [pooledProgramImage, programImageRunWith, List.mapM_cons, List.mapM_nil,
    programEntryRunWith, bytes, source.decoded, bind, Option.bind]
  cases remainder <;> rfl

private theorem pooledDecoded (remainder : Bool) : PooledDecoded (pooled remainder) (pooledProgram remainder) := by
  intro actual member
  simp only [pooled, List.mem_singleton] at member
  subst actual
  change ∃ i : Fin 1, _ = _
  exact ⟨0, by cases remainder <;> decide⟩

private theorem pooledInputs (remainder : Bool) :
    NativeInputs pooledDecoderFields (pooled remainder) (before remainder) cells (pooledProgram remainder) := by
  refine ⟨by decide, ?_, image remainder, ?_, ⟨[0x3fffc], pooledImage remainder⟩, ?_⟩
  · intro cell member
    simp [cells] at member
    rcases member with rfl | rfl | rfl <;> trivial
  · refine ⟨(4, 0), ?_⟩
    have read : run (SailRV32.Functions.get_arch_pc ()) (before remainder) =
        .ok 0x3fffc (before remainder) := by
      apply read_register
      simp [before, initial, wordWriteState, Std.ExtDHashMap.get?_insert]
    rw [initialState, read]
    rfl
  · exact ⟨(boundary remainder (ROM.table cells seed)).initial,
      (boundary remainder (ROM.table cells seed)).aligned,
      (boundary remainder (ROM.table cells seed)).memory⟩

/-- Inhabited per-circuit DIVU/REMU claims for a zero divisor and aliased rs1/rd.
    All bounds, reads and selectors are supplied by initialized shared history. -/
theorem per_circuit_division_soundness [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (remainder : Bool) :
    ∃ input : Airbender.MulDiv.Input,
      (Airbender.MulDiv.circuitModel (pooled remainder) (before remainder) cells (pooledProgram remainder)).relation
        input ⟨⟨if remainder then 7 else 65535, if remainder then 2 else 65535⟩, ⟨0, 4⟩⟩ (row remainder).assignment ∧
      Airbender.MulDiv.InterfaceAssumptions (pooled remainder) (before remainder) cells (pooledProgram remainder) ∧
      Airbender.MulDiv.spec input ⟨⟨if remainder then 7 else 65535, if remainder then 2 else 65535⟩, ⟨0, 4⟩⟩ := by
  have member : (⟨.mulDiv, (row remainder).assignment⟩ : Row babyBearModulus PooledFamily) ∈
      (pooled remainder).rows := by simp [pooled]
  obtain ⟨current, position⟩ := Proofs.pooled_row_position_exists (by decide) (by decide)
    (pooledAccepted remainder) (pooledInputs remainder).clocks (pooledInputs remainder).image
    (pooledInputs remainder).distinct (pooledInputs remainder).aligned
    (pooledImage remainder) (pooledDecoded remainder) member
  let input : Airbender.MulDiv.Input :=
    ⟨if remainder then .remu else .divu, ⟨7, 2⟩, ⟨0, 0⟩, ⟨65532, 3⟩, .Regidx 1, .Regidx 2, .Regidx 1, current⟩
  let output : Output := ⟨⟨if remainder then 7 else 65535, if remainder then 2 else 65535⟩, ⟨0, 4⟩⟩
  have mapping : Airbender.MulDiv.TraceMapping (pooled remainder) (before remainder) cells
      (pooledProgram remainder) input output (row remainder).assignment := by
    refine ⟨?_, position, ?_⟩
    · constructor <;> cases remainder <;> rfl
    · refine ⟨(entry remainder).mapFamily (fun _ => .mulDiv), by simp [pooledProgram], rfl, ?_, ?_⟩
      · cases remainder <;> decide
      · cases remainder <;> rfl
  have assumptions : Airbender.MulDiv.InterfaceAssumptions (pooled remainder) (before remainder) cells
      (pooledProgram remainder) := ⟨pooledInputs remainder, rfl, rfl⟩
  have relation : (Airbender.MulDiv.circuitModel (pooled remainder) (before remainder) cells
      (pooledProgram remainder)).relation input output (row remainder).assignment :=
    ⟨⟨ pooledAccepted remainder, pooledDecoded remainder, member⟩, mapping⟩
  exact ⟨input, relation, assumptions, Airbender.MulDiv.babyBear_soundness (pooled remainder)
    (before remainder) cells (pooledProgram remainder) assumptions input output _ relation⟩

/-- Removing the local PC bound does not permit field-aliased declared PCs. -/
theorem per_circuit_pc_alias_rejected (current : State) :
    ¬ Airbender.MulDiv.TraceMapping (pooled false) (before false) cells (pooledProgram false)
      (⟨.divu, ⟨7, 2⟩, ⟨0, 0⟩, ⟨babyBearModulus + 65532, 3⟩,
        .Regidx 1, .Regidx 2, .Regidx 1, current⟩ : Airbender.MulDiv.Input)
      ⟨⟨65535, 65535⟩, ⟨0, 4⟩⟩ (row false).assignment := by
  intro mapping
  have impossible := mapping.words.pcLo
  change babyBearModulus + 65532 = ((row false).assignment 0).val at impossible
  have small := ZMod.val_lt ((row false).assignment 0)
  omega

end Tests.MulDivTrace
