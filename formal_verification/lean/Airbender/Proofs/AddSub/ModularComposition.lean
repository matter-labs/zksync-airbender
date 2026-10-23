import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.AddSub.ModularNative
import Airbender.Proofs.Trace.PooledComposition
import Airbender.Proofs.Trace.PooledROMView
import Airbender.Review.Trace.Modular

namespace Airbender.AddSub.Modular.Pooled.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem addsub_execution
    (hp : 536870912 ≤ babyBearModulus) (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    (registers : ∀ index, Cell.register index ∈ cells)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : Pooled.programImage initial addresses = some program)
    (decoded : PooledDecoded trace program) (loads : NoDiscardedLoads program)
    {w : Nat → ZMod babyBearModulus} (member : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .addSub)
    (query : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).decoderQuery = entry.query)
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily)).reverse before after) :
    ∃ original, Pooled.clauseFor entry.instruction = some original ∧
      run (normalStep original) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 19).val (w 20).val).toBitVec) := by
  have bounds := (pooled_value_bounds (by omega) inverse accepted clocks image wordSetup subwordSetup
    programImage decoded).1 _ member
  have left := bounds importedConstraintsMemoryPorts[0]
    (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have right := bounds importedConstraintsMemoryPorts[1]
    (by change importedConstraintsMemoryPorts[1] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have old := bounds importedConstraintsMemoryPorts[2]
    (by change importedConstraintsMemoryPorts[2] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have readBounds : (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 29).val (w 30).val).Bounded ∧ (Word.mk (w 31).val (w 32).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using And.intro left (And.intro right old)
  have source := run_program_sources programImage entry present
  obtain original | original | original | original | original := source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · rw [mapped_query] at query
    change (⟨.addSub, w⟩ : Row babyBearModulus).decoderQuery = originalEntry.query at query
    have localFamily : originalEntry.data.family = .addSub := by
      cases mode : originalEntry.data.family
      · rfl
      · simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
    rcases Modular.Proofs.fields_cases originalSource.fields with
      standard | ⟨opcode, rs1, rs2, rd, encoding, data⟩
    · obtain ⟨original, selected, checked⟩ := local_arithmetic_instruction_execution .sail
        (by dsimp [ROM.limit]; omega) inverse image trace.rom.wordMemory trace.memoryEpoch registers
        (accepted.constraints _ member) (accepted.active _ member)
        ⟨readBounds.1, readBounds.2.1, query_immediate (by decide) standard query⟩
        standard localFamily query (fun _ => loads _ present) past history
      exact ⟨original, clause_original selected, checked⟩
    · refine ⟨clause opcode rs1 rs2 rd, ?_, ?_⟩
      · change Pooled.clauseFor originalEntry.instruction = _
        rw [encoding]
        cases opcode <;> rfl
      · have checked := Modular.Proofs.native_execution
          (retired_state_image image (Word.mk (w 0).val (w 1).val).toBitVec)
          registers trace.rom.wordMemory trace.memoryEpoch
          (accepted.constraints _ member) (accepted.active _ member) readBounds query
          opcode rs1 rs2 rd data
          (retired_state_history past (Word.mk (w 0).val (w 1).val).toBitVec)
          (retired_state_history history (Word.mk (w 0).val (w 1).val).toBitVec)
          (retired_state_pc before (Word.mk (w 0).val (w 1).val).toBitVec)
        rw [retired_state_overwrite] at checked
        exact checked
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

theorem row_step
    (hp : 536870912 ≤ babyBearModulus) (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address)
    (memoryConfiguration : FlatMemoryConfiguration initial)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : Pooled.programImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (loads : NoDiscardedLoads program)
    (terminal : trace.terminal.word.Bounded)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0)
    {row : Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    StepWith Pooled.decoderFields Pooled.clauseFor program (retiredState before row.start.word.toBitVec)
      (retiredState after row.finish.word.toBitVec) := by
  have limbSize : limbBase < babyBearModulus := by dsimp [limbBase]; omega
  obtain ⟨entry, present, family, query⟩ := decoder_member (decoded row member)
  have source := pooled_source_after_history (by omega) inverse accepted clocks image
    programImage present (code entry present) native past
  have fetched := native_query_pc_word limbSize query
  change row.start.word = Word.ofBitVec entry.pc at fetched
  have position : row.start.word.toBitVec = entry.pc := by rw [fetched, Word.ofBitVec_roundtrip]
  have pc : run (SailRV32.Functions.get_arch_pc ()) (retiredState before row.start.word.toBitVec) =
      .ok entry.pc (retiredState before row.start.word.toBitVec) := by
    simpa only [position] using retired_state_pc before row.start.word.toBitVec
  refine ⟨entry, present, entry_source_retired_state source _, pc, ?_⟩
  cases row with
  | mk kind w =>
    cases kind with
    | addSub =>
      exact addsub_execution hp inverse accepted clocks image wordSetup subwordSetup
        registers programImage decoded loads member present family query past history
    | mulDiv =>
      obtain ⟨original, selected, checked⟩ := pooled_muldiv_execution hp inverse accepted clocks image wordSetup subwordSetup
        programImage decoded member present family query history
      exact ⟨original, clause_original selected, checked⟩
    | shiftBinop =>
      obtain ⟨original, selected, checked⟩ := pooled_shift_execution hp inverse accepted clocks image
        programImage decoded member present family query history
      exact ⟨original, clause_original selected, checked⟩
    | jumpBranchSlt =>
      obtain ⟨original, selected, checked⟩ := pooled_control_execution hp inverse accepted clocks image wordSetup subwordSetup
        programImage decoded (fun entry present => (code entry present).2) terminal
        member present family query past history isa configuration
      exact ⟨original, clause_original selected, checked⟩
    | wordMemory =>
      obtain ⟨original, selected, checked⟩ := pooled_word_execution hp inverse accepted clocks image wordSetup subwordSetup
        aligned ordinary memoryConfiguration programImage decoded member present family query native past history
      exact ⟨original, clause_original selected, checked⟩
    | subwordMemory =>
      obtain ⟨original, selected, checked⟩ := pooled_subword_execution hp inverse accepted clocks image wordSetup subwordSetup
        aligned ordinary memoryConfiguration programImage decoded member present family query native past history
      exact ⟨original, clause_original selected, checked⟩

theorem trace_execution
    (hp : 536870912 ≤ babyBearModulus) (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} {initial : State} {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledInputs trace initial cells program Pooled.decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program) :
    Realizes (Pooled.Step program) trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < babyBearModulus := by dsimp [timestampBase]; omega
  have limbSize : limbBase < babyBearModulus := by dsimp [limbBase]; omega
  obtain ⟨timestamp, initialBound⟩ := inputs.initialPC
  obtain ⟨addresses, programImage⟩ := inputs.programImage
  have initialRead := initial_state_pc limbSize initialBound
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    pooled_native_history clockSize inverse accepted inputs.clocks inputs.image
      inputs.distinct inputs.aligned programImage decoded
  have chain := ordered_row_boundaries clockSize inverse accepted inputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection clockSize inverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := compose_native_rows initialRead
    (fun row member {before after events} native past current =>
      row_step hp inverse accepted inputs.clocks inputs.image inputs.wordSetup inputs.subwordSetup
        inputs.registers inputs.aligned inputs.ordinary inputs.configuration programImage decoded inputs.code
        inputs.loads (VerifierBoundary.Proofs.trace_terminal_bound limbSize accepted inputs.verifierBoundary) inputs.configuration.isa
        ⟨inputs.configuration.privilege, inputs.landingPadDisabled⟩ member native past current)
    rows trace.terminal (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  exact native_trace_postconditions clockSize inverse accepted inputs.clocks
    inputs.image inputs.distinct initialRead consistent chain nativeHistory matchedState execution

theorem native_trace_execution
    {trace : PooledTrace babyBearModulus} {before : State} {cells : List Cell} {program : List PooledProgramEntry}
    (inputs : PooledBootInputs trace before cells program Pooled.decoderFields)
    (accepted : Accepted trace) (decoded : PooledDecoded trace program) :
    Realizes (Pooled.Step program) trace before cells (ROMView.token before) := by
  have clockSize : 2 * timestampBase + 4 < babyBearModulus := by decide
  have size : 4 < babyBearModulus := by decide
  have clocks := ROMView.native_clocks size inputs.seed inputs.initialBoundary
  obtain ⟨after, execution, pc, terminal⟩ := trace_execution (by decide) (by decide)
    (PooledROMView.execution_boundary size inputs)
    (PooledROMView.accepted clockSize (by decide) before accepted clocks inputs.seed)
    (PooledROMView.decoded before decoded)
  refine ⟨after, execution, pc, ?_⟩
  intro sink member
  have lifted := terminal (ROMView.token before sink) (List.mem_map_of_mem member)
  simpa only [ROMView.token_address, id_eq] using lifted

end Airbender.AddSub.Modular.Pooled.Proofs
