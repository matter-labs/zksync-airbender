import Airbender.Proofs.Reduced.WordTransport

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- LW/SW retirement uses actual shared operands, locations and readonly-ROM history. -/
theorem word_execution_from_shared_history
    (hp : FieldCapacity.NativeWordCapacity babyBearModulus)
    (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address)
    (configuration : FlatMemoryConfiguration initial)
    {w : Nat → ZMod babyBearModulus} {entry : PooledProgramEntry}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      ((⟨.wordMemory, w⟩ : Row babyBearModulus PooledFamily).constraints trace.rom))
    (active : w WordMemory.importedConstraintsTraceColumns.execute = 1)
    (sourceBound : (readToken w WordMemory.importedConstraintsMemoryPorts[0]).word.Bounded)
    (addresses : ∀ port ∈ WordMemory.importedConstraintsMemoryPorts,
      ∃ cell ∈ cells, port.address.code w = cell.addressCode)
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .wordMemory)
    (query : (⟨.wordMemory, w⟩ : Row babyBearModulus PooledFamily).decoderQuery = entry.query)
    {before after : State} {events : List MemoryAccess} (epoch : Nat)
    (readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents epoch (⟨.wordMemory, w⟩ : Row babyBearModulus PooledFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 11).val (w 12).val).toBitVec) := by
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left (WordMemory.importedConstraints trace.rom.wordMemory)
      WordMemory.importedConstraintsTimestampLookups)
  have limbSize : limbBase < babyBearModulus := by dsimp [limbBase]; omega
  have romSize : ROM.limit < babyBearModulus := by dsimp [ROM.limit]; omega
  have arithmeticInverse : SerializedInverse.Limb16 babyBearModulus := by
    calc
      (-30720 : ZMod babyBearModulus) * 65536 = (-3840 : ZMod babyBearModulus) * 524288 := by ring
      _ = 1 := inverse
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
    word_address_from_shared_history hp inverse core sourceBound addresses source family query store selected
  have transfer (store : Bool) (selected : w 10 = if store then 1 else 0) :=
    word_transport_from_shared_history addresses store selected epoch prepared
  have romReads : ROM.Reads
      { retiredState before currentPC with regs :=
        (retiredState before currentPC).regs.insert .nextPC (currentPC + 4) }
      trace.rom.wordMemory := by
    rw [wordSetup]
    exact rom_reads_after_history (by dsimp [ROM.limit]; omega) preparedImage aligned preparedPast readonly
  obtain original | original | original | original | original := AddSub.Modular.External.Proofs.source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · have mode : originalEntry.data.family = .wordMemory := by
      cases mode : originalEntry.data.family
      · simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
      · rfl
    rw [mapped_query] at query
    change (⟨.wordMemory, w⟩ : Row babyBearModulus).decoderQuery = originalEntry.query at query
    have selector := row_query_selectors_of_bound limbSize trace.rom.wordMemory
      (row := (⟨.wordMemory, w⟩ : Row babyBearModulus)) constraints
      (AddSub.Modular.External.Proofs.decoderRules.bounds _ _ originalSource.fields).2 query
      ⟨0, by change 0 < 1; decide⟩
    change w 10 = if originalEntry.data.mask.testBit 0 then 1 else 0 at selector
    have fields := AddSub.Modular.External.Proofs.memory_fields originalSource.fields mode
    unfold Trace.decoderFields at fields
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
          exact local_word_load_execution romSize core disabled active selected
            (AddSub.Modular.External.Proofs.memory_fields originalSource.fields mode) mode query encoding epoch aligned ordinary
            (addressFor false selected) preparedConfiguration romReads prepared (transfer false selected)
    case h_7 =>
      rename_i _ imm rs2 rs1 encoding
      have selected : w 10 = 1 := by simpa [← Option.some.inj fields] using selector
      refine ⟨SailRV32.Functions.execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4, ?_, ?_⟩
      · change instructionClause originalEntry.instruction = _
        rw [encoding]; rfl
      · apply finish
        have transport := local_word_transport romSize core disabled epoch aligned ordinary
          true selected query (addressFor true selected) preparedConfiguration prepared (transfer true selected)
        exact local_word_store_execution limbSize (AddSub.Modular.External.Proofs.memory_fields originalSource.fields mode) query encoding transport
    case h_8 => cases fields
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

end Airbender.AddSub.Modular.External.Caller.Proofs
