import Airbender.Proofs.AddSub.ModularExternalExecution
import Airbender.Proofs.Reduced.StreamMemory

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail Trace.Proofs
open AddSub.Modular.External.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Arithmetic, modular and external clauses use actual shared-history operands. -/
theorem addsub_execution_from_shared_history
    (hp : 536870912 ≤ babyBearModulus) (inverse : SerializedInverse.Clock babyBearModulus)
    {trace : PooledTrace babyBearModulus} {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    {w : Nat → ZMod babyBearModulus} {entry : PooledProgramEntry}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      ((⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).constraints trace.rom))
    (active : w AddSub.importedConstraintsTraceColumns.execute = 1)
    (bounds : ∀ port ∈ AddSub.importedConstraintsMemoryPorts, (readToken w port).word.Bounded)
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .addSub)
    (query : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).decoderQuery = entry.query)
    (loads : ∀ (imm : BitVec 12) (rs1 : BitVec 5),
      entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4))
    {stream : List (BitVec 32)} {position : Nat}
    (port : External.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) = true →
      stream[position]? = some (External.response (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily)))
    {before after : State} {events : List MemoryAccess} (epoch : Nat)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents epoch (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily)).reverse before after) :
    ∃ original, External.clause stream position entry.instruction =
      some (original, position + if External.isRead (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) then 1 else 0) ∧
      run (normalStep original) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 19).val (w 20).val).toBitVec) := by
  have limbSize : limbBase < babyBearModulus := by dsimp [limbBase]; omega
  have core := constraints
  have left := bounds AddSub.importedConstraintsMemoryPorts[0]
    (by simp [AddSub.importedConstraintsMemoryPorts])
  have right := bounds AddSub.importedConstraintsMemoryPorts[1]
    (by simp [AddSub.importedConstraintsMemoryPorts])
  have readBounds : (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 29).val (w 30).val).Bounded := by
    simpa [read_word, AddSub.importedConstraintsMemoryPorts] using And.intro left right
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
          (by dsimp [ROM.limit]; omega) inverse image trace.rom.wordMemory epoch registers
          core active
          ⟨readBounds.1, readBounds.2, query_immediate limbSize standard query⟩
          standard localFamily query (fun _ => loads) past history
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
            (by dsimp [ROM.limit]; omega) inverse epoch core canonical data query
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
          (by dsimp [ROM.limit]; omega) inverse image trace.rom.wordMemory epoch registers
          core active
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
        (by simp [AddSub.importedConstraintsMemoryPorts])
      have oldBounds : (Word.mk (w 31).val (w 32).val).Bounded := by
        simpa [read_word, AddSub.importedConstraintsMemoryPorts] using old
      refine ⟨Modular.clause opcode rs1 rs2 rd, ?_, ?_⟩
      · change External.clause stream position originalEntry.instruction = _
        rw [encoding, unread]
        cases opcode <;> rfl
      · have checked := Modular.Proofs.native_execution
          (retired_state_image image (Word.mk (w 0).val (w 1).val).toBitVec)
          registers trace.rom.wordMemory epoch core active
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

end Airbender.AddSub.Modular.External.Caller.Proofs
