import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.AddSub.ModularExternalDecoder
import Airbender.Proofs.AddSub.ModularNative
import Airbender.Proofs.Trace.PooledComposition
import Airbender.Proofs.Trace.OracleExecution

namespace Airbender.AddSub.Modular.External.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Trace.Proofs
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem addsub_execution
    (hp : 536870912 ≤ babyBearModulus) (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    (registers : ∀ index, Cell.register index ∈ cells)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : External.programImage initial addresses = some program)
    (decoded : PooledDecoded trace program) (loads : NoDiscardedLoads program)
    {w : Nat → ZMod babyBearModulus} (member : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .addSub)
    (query : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).decoderQuery = entry.query)
    {stream : List (BitVec 32)} {position : Nat}
    (port : External.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) = true →
      stream[position]? = some (External.response (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily)))
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily)).reverse before after) :
    ∃ original, External.clause stream position entry.instruction =
      some (original, position + if External.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) then 1 else 0) ∧
      run (normalStep original) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 19).val (w 20).val).toBitVec) := by
  have limbSize : limbBase < babyBearModulus := by dsimp [limbBase]; omega
  have core := accepted.constraints _ member
  have bounds := (pooled_value_bounds (by omega) inverse accepted clocks image wordSetup subwordSetup
    programImage decoded).1 _ member
  have left := bounds AddSub.importedConstraintsMemoryPorts[0]
    (by change AddSub.importedConstraintsMemoryPorts[0] ∈ AddSub.importedConstraintsMemoryPorts
        simp [AddSub.importedConstraintsMemoryPorts])
  have right := bounds AddSub.importedConstraintsMemoryPorts[1]
    (by change AddSub.importedConstraintsMemoryPorts[1] ∈ AddSub.importedConstraintsMemoryPorts
        simp [AddSub.importedConstraintsMemoryPorts])
  have readBounds : (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 29).val (w 30).val).Bounded := by
    simpa [read_word, AddSub.importedConstraintsMemoryPorts] using And.intro left right
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
    have flags := row_query_selectors_of_bound limbSize trace.rom.wordMemory core
      (field_bounds originalSource.fields).2 query
    have flag := flags ⟨8, by change 8 < 9; decide⟩
    change w 18 = if originalEntry.data.mask.testBit 8 then 1 else 0 at flag
    have classified : External.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) =
        originalEntry.data.mask.testBit 8 := by
      simp only [External.isRead, NonDeterminism.Pooled.isRead, NonDeterminism.isRead, flag]
      cases originalEntry.data.mask.testBit 8 <;> simp
    rcases arithmetic_cases originalSource.fields with oracle | custom
    · rcases NonDeterminism.Proofs.fields_cases oracle with
        standard | ⟨rd, nonzero, encoding, data⟩ | ⟨rs1, nonzero, encoding, data⟩
      · have small := (decoder_field_bounds standard).2
        have division : originalEntry.data.mask / 256 = 0 := Nat.div_eq_of_lt (by omega)
        have unread : External.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) = false := by
          rw [classified]
          simp [Nat.testBit, Nat.shiftRight_eq_div_pow, division]
        obtain ⟨original, selected, checked⟩ := local_arithmetic_instruction_execution .sail
          (by dsimp [ROM.limit]; omega) inverse image trace.rom.wordMemory trace.memoryEpoch registers
          core (accepted.active _ member)
          ⟨readBounds.1, readBounds.2, query_immediate limbSize standard query⟩
          standard localFamily query (fun _ => loads _ present) past history
        refine ⟨original, ?_, checked⟩
        simpa [unread, ProgramEntry.mapFamily] using (clause_standard standard selected)
      · have selectedRead : External.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) = true := by
          rw [classified, data]
          norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
        have supplied := port selectedRead
        let value := External.response (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily)
        refine ⟨writeResult (.Regidx rd) (Word.ofBitVec value), ?_, ?_⟩
        · change External.clause stream position originalEntry.instruction = _
          rw [encoding]
          simp [External.clause, NonDeterminism.clause, supplied, selectedRead, value]
          exact nonzero
        · have canonical : (Word.mk (w 0).val (w 1).val).Bounded := by
            have pc : (Word.mk (w 0).val (w 1).val) = Word.ofBitVec originalEntry.pc :=
              native_query_pc_word limbSize query
            rw [pc]
            exact Word.ofBitVec_bound _
          have checked := NonDeterminism.Proofs.local_read_execution
            (by dsimp [ROM.limit]; omega) inverse trace.memoryEpoch core canonical data query
            (retired_state_history history (Word.mk (w 0).val (w 1).val).toBitVec)
            (retired_state_pc before (Word.mk (w 0).val (w 1).val).toBitVec)
          rw [retired_state_overwrite] at checked
          exact checked
      · have unread : External.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) = false := by
          rw [classified, data]
          norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
        let nop : ProgramEntry := { originalEntry with instruction := .ITYPE (0, .Regidx 0, .Regidx 0, .ADDI) }
        have nopFields : Trace.decoderFields nop.instruction = some nop.data := by
          change some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ = some originalEntry.data
          rw [data]
        obtain ⟨original, selected, checked⟩ := local_arithmetic_instruction_execution .sail
          (by dsimp [ROM.limit]; omega) inverse image trace.rom.wordMemory trace.memoryEpoch registers
          core (accepted.active _ member)
          ⟨readBounds.1, readBounds.2, query_immediate limbSize nopFields query⟩
          nopFields localFamily (entry := nop) query (by intro _ imm rs1; simp [nop]) past history
        change some (SailRV32.Functions.execute_ITYPE 0 (.Regidx 0) (.Regidx 0) .ADDI) =
          some original at selected
        have nopClause : SailRV32.Functions.execute_ITYPE 0 (.Regidx 0) (.Regidx 0) .ADDI =
            (pure SailRV32.Functions.RETIRE_SUCCESS : SailRV32.SailM _) := by rfl
        rw [(Option.some.inj selected).symm.trans nopClause] at checked
        refine ⟨pure SailRV32.Functions.RETIRE_SUCCESS, ?_, checked⟩
        change External.clause stream position originalEntry.instruction = _
        rw [encoding]
        simp [External.clause, NonDeterminism.clause, unread]
        exact nonzero
    · obtain ⟨opcode, rs1, rs2, rd, encoding, data⟩ := custom
      have unread : External.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) = false := by
        rw [classified, data]
        unfold nativeData arithmeticFields
        split
        · change (1 : Nat).testBit 8 = false
          decide
        · change (2 ^ (opcode.selector - 10)).testBit 8 = false
          cases opcode <;> decide
      have old := bounds AddSub.importedConstraintsMemoryPorts[2]
        (by change AddSub.importedConstraintsMemoryPorts[2] ∈ AddSub.importedConstraintsMemoryPorts
            simp [AddSub.importedConstraintsMemoryPorts])
      have oldBounds : (Word.mk (w 31).val (w 32).val).Bounded := by
        simpa [read_word, AddSub.importedConstraintsMemoryPorts] using old
      refine ⟨Modular.clause opcode rs1 rs2 rd, ?_, ?_⟩
      · change External.clause stream position originalEntry.instruction = _
        rw [encoding, unread]
        cases opcode <;> rfl
      · have checked := Modular.Proofs.native_execution
          (retired_state_image image (Word.mk (w 0).val (w 1).val).toBitVec)
          registers trace.rom.wordMemory trace.memoryEpoch core (accepted.active _ member)
          ⟨readBounds.1, readBounds.2, oldBounds⟩ query opcode rs1 rs2 rd data
          (retired_state_history past (Word.mk (w 0).val (w 1).val).toBitVec)
          (retired_state_history history (Word.mk (w 0).val (w 1).val).toBitVec)
          (retired_state_pc before (Word.mk (w 0).val (w 1).val).toBitVec)
        rw [retired_state_overwrite] at checked
        exact checked
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

set_option backward.isDefEq.respectTransparency false in
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
    (programImage : External.programImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    (code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0)
    (loads : NoDiscardedLoads program) (terminal : trace.terminal.word.Bounded)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0)
    {stream : List (BitVec 32)} (ports : External.StreamPorts trace stream)
    {row : Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after) :
    External.Step stream program
      (retiredState before row.start.word.toBitVec, External.readIndex trace row)
      (retiredState after row.finish.word.toBitVec,
        External.readIndex trace row + if External.isRead row then 1 else 0) := by
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
      exact addsub_execution hp inverse accepted clocks image wordSetup subwordSetup registers
        programImage decoded loads member present family query (ports _ member) past history
    | mulDiv =>
      obtain ⟨original, selected, checked⟩ := pooled_muldiv_execution hp inverse accepted clocks
        image wordSetup subwordSetup programImage decoded member present family query history
      exact ⟨original, clause_original selected, checked⟩
    | shiftBinop =>
      obtain ⟨original, selected, checked⟩ := pooled_shift_execution hp inverse accepted clocks
        image programImage decoded member present family query history
      exact ⟨original, clause_original selected, checked⟩
    | jumpBranchSlt =>
      obtain ⟨original, selected, checked⟩ := pooled_control_execution hp inverse accepted clocks
        image wordSetup subwordSetup programImage decoded (fun entry present => (code entry present).2)
        terminal member present family query past history isa configuration
      exact ⟨original, clause_original selected, checked⟩
    | wordMemory =>
      obtain ⟨original, selected, checked⟩ := pooled_word_execution hp inverse accepted clocks
        image wordSetup subwordSetup aligned ordinary memoryConfiguration programImage decoded
        member present family query native past history
      exact ⟨original, clause_original selected, checked⟩
    | subwordMemory =>
      obtain ⟨original, selected, checked⟩ := pooled_subword_execution hp inverse accepted clocks
        image wordSetup subwordSetup aligned ordinary memoryConfiguration programImage decoded
        member present family query native past history
      exact ⟨original, clause_original selected, checked⟩

end Airbender.AddSub.Modular.External.Proofs
