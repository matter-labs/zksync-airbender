import Airbender.Proofs.Trace.PooledCode
import Airbender.Proofs.Trace.WordMemory
import Airbender.Review.Trace.Execution

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail

set_option backward.isDefEq.respectTransparency false in
/-- Effective addresses and their initialized RAM cells come from the pooled
    read/address history and actual decoder query, including cross-family reads. -/
theorem pooled_word_address {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    [registry : PooledRegistry projection]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : programImageRunWith projection initial addresses = some program)
    (decoded : PooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row p PooledFamily).decoderQuery = entry.query)
    (store : Bool) (selected : w 10 = if store then 1 else 0) :
    let address := Word.mk (w (if store then 25 else 19)).val (w (if store then 26 else 20)).val
    address.Bounded ∧ address.toBitVec = (Word.mk (w 17).val (w 18).val).toBitVec +
      (Word.mk (w 8).val (w 9).val).toBitVec ∧ Cell.ram address.toBitVec ∈ cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  have source := (pooled_value_bounds (by omega) inverse accepted clocks image wordSetup subwordSetup
    programImage decoded).1 _ member WordMemory.importedConstraintsMemoryPorts[0]
    (by change WordMemory.importedConstraintsMemoryPorts[0] ∈ WordMemory.importedConstraintsMemoryPorts
        simp [WordMemory.importedConstraintsMemoryPorts])
  have sourceBound : (Word.mk (w 17).val (w 18).val).Bounded := by
    simpa [read_word, WordMemory.importedConstraintsMemoryPorts] using source
  have fetched := run_program_sources programImage entry present
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    obtain original | original | original | original | original := registry.sourceCases fetched
    all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
    all_goals subst entry
    · rw [mapped_query] at query
      change (⟨.wordMemory, w⟩ : Row p).decoderQuery = originalEntry.query at query
      have mode : originalEntry.data.family = .wordMemory := by
        cases mode : originalEntry.data.family
        · simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
        · rfl
      exact query_immediate limbSize (row := (⟨.wordMemory, w⟩ : Row p))
        (registry.memoryFields originalSource.fields mode) query
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (WordMemory.importedConstraints trace.rom.wordMemory)
      WordMemory.importedConstraintsTimestampLookups)
  cases store
  all_goals dsimp only [Bool.false_eq_true, if_false, if_true] at selected ⊢
  · have portMember : WordMemory.importedConstraintsMemoryPorts[1] ∈
        (⟨.wordMemory, w⟩ : Row p PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[1] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have bound := address_bounds clockSize inverse accepted clocks image _ member _ portMember
    have cell := row_ram_cell clockSize inverse accepted clocks image member portMember
      (by refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    exact local_word_address (by dsimp [ROM.limit]; omega) inverse core false selected
      sourceBound immediateBound bound cell.1
  · have portMember : WordMemory.importedConstraintsMemoryPorts[2] ∈
        (⟨.wordMemory, w⟩ : Row p PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[2] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have bound := address_bounds clockSize inverse accepted clocks image _ member _ portMember
    have cell := row_ram_cell clockSize inverse accepted clocks image member portMember
      (by refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    exact local_word_address (by dsimp [ROM.limit]; omega) inverse core true selected
      sourceBound immediateBound bound cell.1

set_option backward.isDefEq.respectTransparency false in
/-- The same pooled grouped history realizes actual Sail word-RAM accesses.
    Canonical addresses are recovered from initialized cells, not assumed. -/
theorem pooled_word_native_transport {p : Nat} [Fact p.Prime]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows)
    (store : Bool) (selected : w 10 = if store then 1 else 0)
    {before after : State}
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p PooledFamily)).reverse before after) :
    if store then
      run (writeMemory (size := 4) (Word.mk (w 25).val (w 26).val).toBitVec
        (Word.mk (w 31).val (w 32).val).toBitVec) before = .ok () after
    else
      (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4
        (Word.mk (w 19).val (w 20).val).toBitVec.toNat).run before =
        .ok (Word.mk (w 23).val (w 24).val).toBitVec before := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have oneValue : (1 : ZMod p).val = 1 := by
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (by omega : 1 < p)
  cases store
  · simp only [Bool.false_eq_true, if_false] at selected ⊢
    have present : WordMemory.importedConstraintsMemoryPorts[1] ∈
        (⟨.wordMemory, w⟩ : Row p PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[1] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have cell := row_ram_cell clockSize inverse accepted clocks image member present
      (by refine ⟨Nat.pair (w 19).val (w 20).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    have read := native_history_read trace.memoryEpoch rfl rfl rfl history present cell.2
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord, MemoryAddress.word, Cell.read] using read
  · simp only [if_true] at selected ⊢
    have present : WordMemory.importedConstraintsMemoryPorts[2] ∈
        (⟨.wordMemory, w⟩ : Row p PooledFamily).ports := by
      change WordMemory.importedConstraintsMemoryPorts[2] ∈ WordMemory.importedConstraintsMemoryPorts
      simp [WordMemory.importedConstraintsMemoryPorts]
    have cell := row_ram_cell clockSize inverse accepted clocks image member present
      (by refine ⟨Nat.pair (w 25).val (w 26).val, ?_⟩
          simp [WordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, selected, pairCode, oneValue])
    have written := native_history_write trace.memoryEpoch rfl rfl rfl history rfl cell.2
    simpa [WordMemory.importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord, MemoryAddress.word, Cell.write] using written

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- LW/SW execute on the same pooled state used by every other family. All
    operands, effective addresses and native/ROM reads are derived internally. -/
theorem pooled_word_execution {p : Nat} [Fact p.Prime]
    {projection : SailRV32.instruction → Option (DecoderData PooledFamily)}
    [registry : PooledRegistry projection]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    {values : Nat → BitVec 32} (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable values)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : programImageRunWith projection initial addresses = some program)
    (decoded : PooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.wordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row p PooledFamily).decoderQuery = entry.query)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.wordMemory, w⟩ : Row p PooledFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 11).val (w 12).val).toBitVec) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have romSize : ROM.limit < p := by dsimp [ROM.limit]; omega
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (WordMemory.importedConstraints trace.rom.wordMemory)
      WordMemory.importedConstraintsTimestampLookups)
  have disabled : ∀ query, trace.rom.wordMemory.Contains #[] query → query[8] = 0 →
      query[1] = 0 ∧ query[2] = 0 := by
    intro query contains inactive
    exact ROM.Proofs.disabled (by omega) image (by rwa [wordSetup] at contains) inactive
  have canonical := native_query_pc_word limbSize query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at canonical
  have bound : (Word.mk (w 0).val (w 1).val).Bounded := canonical.symm ▸ Word.ofBitVec_bound entry.pc
  have successor := (WordMemory.Proofs.pc_successor (by omega) arithmeticInverse core
    (initial := Word.mk (w 0).val (w 1).val) (final := Word.mk (w 11).val (w 12).val)
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ bound).2.2
  let currentPC := (Word.mk (w 0).val (w 1).val).toBitVec
  have prepared := sail_history_control (retired_state_history history currentPC) .nextPC (.inr rfl) (currentPC + 4)
  have preparedPast := sail_history_control (retired_state_history past currentPC) .nextPC (.inr rfl) (currentPC + 4)
  have preparedImage := initial_image_control (retired_state_image image currentPC) .nextPC (.inr rfl) (currentPC + 4)
  have preparedConfiguration := configuration_next_pc_write
    (retired_state_configuration (history_configuration past configuration) currentPC) (currentPC + 4)
  have finish (clause : SailRV32.SailM SailRV32.ExecutionResult)
      (executed : run clause
        { retiredState before currentPC with regs := (retiredState before currentPC).regs.insert .nextPC (currentPC + 4) } =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          { retiredState after currentPC with regs := (retiredState after currentPC).regs.insert .nextPC (currentPC + 4) }) :
      run (normalStep clause) (retiredState before currentPC) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after (Word.mk (w 11).val (w 12).val).toBitVec) := by
    have normal := normal_step_native clause (retired_state_pc before currentPC) executed
    change run (normalStep clause) (retiredState before currentPC) =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState (retiredState after currentPC) (currentPC + 4)) at normal
    rw [← successor, retired_state_overwrite] at normal
    exact normal
  have addressFor (store : Bool) (selected : w 10 = if store then 1 else 0) :=
    pooled_word_address hp inverse accepted clocks image wordSetup subwordSetup programImage decoded
      member present family query store selected
  have transfer (store : Bool) (selected : w 10 = if store then 1 else 0) :=
    pooled_word_native_transport (by omega) inverse accepted clocks preparedImage member store selected prepared
  have romReads := pooled_rom_reads_after_history (by omega) inverse accepted clocks
    preparedImage aligned wordSetup native preparedPast
  have source := run_program_sources programImage entry present
  obtain original | original | original | original | original := registry.sourceCases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · have mode : originalEntry.data.family = .wordMemory := by
      cases mode : originalEntry.data.family
      · simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
      · rfl
    rw [mapped_query] at query
    change (⟨.wordMemory, w⟩ : Row p).decoderQuery = originalEntry.query at query
    have selector := row_query_selectors_of_bound limbSize trace.rom.wordMemory
      (row := (⟨.wordMemory, w⟩ : Row p)) (accepted.constraints _ member)
      (registry.rules.bounds _ _ originalSource.fields).2 query
      ⟨0, by change 0 < 1; decide⟩
    change w 10 = if originalEntry.data.mask.testBit 0 then 1 else 0 at selector
    have fields := registry.memoryFields originalSource.fields mode
    unfold decoderFields at fields
    split at fields
    case h_1 | h_2 | h_3 | h_4 | h_5 =>
      simp only [Option.some.injEq] at fields
      rw [← fields] at mode
      unfold arithmeticFields at mode
      split at mode <;> cases mode
    case h_6 =>
      rename_i _ imm rs1 rd encoding
      change (if (rd : BitVec 5) = 0 then _ else _) = some originalEntry.data at fields
      split at fields
      · simp only [Option.some.injEq] at fields
        rw [← fields] at mode
        cases mode
      · have selected : w 10 = 0 := by simpa [← Option.some.inj fields] using selector
        refine ⟨SailRV32.Functions.execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 4, ?_, ?_⟩
        · change instructionClause originalEntry.instruction = _
          rw [encoding]; rfl
        · apply finish
          exact local_word_load_execution romSize core disabled (accepted.active _ member) selected
            (registry.memoryFields originalSource.fields mode) mode query encoding trace.memoryEpoch aligned ordinary
            (addressFor false selected) preparedConfiguration romReads prepared (transfer false selected)
    case h_7 =>
      rename_i _ imm rs2 rs1 encoding
      have selected : w 10 = 1 := by simpa [← Option.some.inj fields] using selector
      refine ⟨SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4, ?_, ?_⟩
      · change instructionClause originalEntry.instruction = _
        rw [encoding]; rfl
      · apply finish
        have transport := local_word_transport romSize core disabled trace.memoryEpoch aligned ordinary
          true selected query (addressFor true selected) preparedConfiguration prepared (transfer true selected)
        exact local_word_store_execution limbSize (registry.memoryFields originalSource.fields mode) query encoding transport
    case h_8 => cases fields
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

end Airbender.Trace.Proofs
