import Airbender.Proofs.Trace.PooledCode
import Airbender.Proofs.SubwordMemory.Execution

namespace Airbender.Trace.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

set_option backward.isDefEq.respectTransparency false in
/-- The same initialized pooled domain supplies the canonical subword RAM
    port, for loads and stores. No per-row address bound is assumed. -/
theorem pooled_subword_cell {p : Nat} [Fact p.Prime]
    (hp : 2 * timestampBase + 4 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell} (image : initialImage initial cells = some trace.initialMemory)
    {w : Nat → ZMod p} (member : (⟨.subwordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows)
    (store : Bool) (selected : w 10 = if store then 1 else 0) :
    let port := if store then SubwordMemory.importedConstraintsMemoryPorts[2]
      else SubwordMemory.importedConstraintsMemoryPorts[1]
    (port.address.word w).Bounded ∧ Cell.ram (port.address.word w).toBitVec ∈ cells ∧
      port.address.code w = (Cell.ram (port.address.word w).toBitVec).addressCode := by
  have present : (if store then SubwordMemory.importedConstraintsMemoryPorts[2]
      else SubwordMemory.importedConstraintsMemoryPorts[1]) ∈
      (⟨.subwordMemory, w⟩ : Row p PooledFamily).ports := by
    change _ ∈ SubwordMemory.importedConstraintsMemoryPorts
    cases store <;> simp [SubwordMemory.importedConstraintsMemoryPorts]
  refine ⟨address_bounds hp inverse accepted clocks image _ member _ present, ?_⟩
  apply row_ram_cell hp inverse accepted clocks image member present
  cases store with
  | false =>
    refine ⟨Nat.pair (w 21).val (w 22).val, ?_⟩
    simp [SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, selected, ZMod.val_one]
  | true =>
    refine ⟨Nat.pair (w 27).val (w 28).val, ?_⟩
    simp [SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode, selected, ZMod.val_one]

set_option backward.isDefEq.respectTransparency false in
/-- Shared history supplies the subword address operands and containing-cell
    bounds. The imported equations recover the exact aligned cell and offset. -/
theorem pooled_subword_address {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell} (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program) (decoded : PooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.subwordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : SubwordMemory.ProgramEntry} (fields : SubwordMemory.decoderFields entry.instruction = some entry.data)
    (query : SubwordMemory.decoderQuery w = entry.query) (store : Bool) (selected : w 10 = if store then 1 else 0) :
    let cell : Word := ⟨(if store then w 27 else w 21).val, (if store then w 28 else w 22).val⟩
    let offset := (w 35).val + 2 * (w 36).val
    cell.Bounded ∧ cell.value % 4 = 0 ∧ offset < 4 ∧
      cell.toBitVec + BitVec.ofNat 32 offset =
        (Word.mk (w 19).val (w 20).val).toBitVec + (Word.mk (w 8).val (w 9).val).toBitVec ∧
      ((Word.mk (w 19).val (w 20).val).toBitVec +
        (Word.mk (w 8).val (w 9).val).toBitVec).toNat % 4 = offset ∧ Cell.ram cell.toBitVec ∈ cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (SubwordMemory.importedConstraints trace.rom.subwordMemory)
      SubwordMemory.importedConstraintsTimestampLookups)
  have source := (pooled_value_bounds (by omega) inverse accepted clocks image wordSetup subwordSetup
    programImage decoded).1 _ member SubwordMemory.importedConstraintsMemoryPorts[0]
    (by change _ ∈ SubwordMemory.importedConstraintsMemoryPorts; simp [SubwordMemory.importedConstraintsMemoryPorts])
  have immediate := native_query_immediate_word (by dsimp [limbBase]; omega)
    (SubwordMemory.Proofs.decoder_field_bounds fields).1 query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at immediate
  have cell := pooled_subword_cell clockSize inverse accepted clocks image member store selected
  apply SubwordMemory.Proofs.local_address (by omega) inverse core store selected
    (by simpa [read_word, SubwordMemory.importedConstraintsMemoryPorts] using source)
    (immediate.symm ▸ (SubwordMemory.Proofs.decoder_field_bounds fields).1)
  · cases store <;> simpa [SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.word] using cell.1
  · cases store <;> simpa [SubwordMemory.importedConstraintsMemoryPorts, MemoryAddress.word] using cell.2.1

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- All six subword instructions retire through original Sail on the pooled
    state. Global history discharges ranges/reads; ROM rows use public byte words. -/
theorem pooled_subword_execution {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : PooledTrace p} (accepted : Accepted trace) (clocks : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial)
    {addresses : List (BitVec 32)} {program : List PooledProgramEntry}
    (programImage : pooledProgramImage initial addresses = some program)
    (decoded : PooledDecoded trace program)
    {w : Nat → ZMod p} (member : (⟨.subwordMemory, w⟩ : Row p PooledFamily) ∈ trace.rows)
    {entry : PooledProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .subwordMemory)
    (query : (⟨.subwordMemory, w⟩ : Row p PooledFamily).decoderQuery = entry.query)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.subwordMemory, w⟩ : Row p PooledFamily)).reverse before after) :
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (SubwordMemory.importedConstraints trace.rom.subwordMemory)
      SubwordMemory.importedConstraintsTimestampLookups)
  rw [subwordSetup] at core
  have bounds : ∀ port ∈ SubwordMemory.importedConstraintsMemoryPorts, (readToken w port).word.Bounded := by
    intro port present
    exact (pooled_value_bounds (by omega) inverse accepted clocks image wordSetup subwordSetup
      programImage decoded).1 _ member port present
  have romReads := pooled_subword_rom_reads (by omega) inverse accepted clocks image aligned native past
  have source := run_program_sources programImage entry present
  obtain original | original | original | original | original := pooled_source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · cases mode : originalEntry.data.family <;>
      simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · rw [mapped_query] at query
    change SubwordMemory.decoderQuery w = originalEntry.query at query
    have operation (store byte signed : Bool) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
        (encoding : originalEntry.instruction = SubwordMemory.Proofs.rowInstruction store byte signed imm rs1 rs2 rd) :
        ∃ clause, instructionClause originalEntry.instruction = some clause ∧
          run (normalStep clause) (retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
            .ok SailRV32.Functions.RETIRE_SUCCESS
              (retiredState after (Word.mk (w 13).val (w 14).val).toBitVec) := by
      have shape := SubwordMemory.Proofs.row_decoder_shape store byte signed imm rs1 rs2 rd encoding originalSource.fields
      have flags := SubwordMemory.Proofs.decoder_selectors limbSize core
        (SubwordMemory.Proofs.decoder_field_bounds originalSource.fields).2.1 query
      have selected : w 10 = if store then 1 else 0 := by
        have flag := flags 0
        cases store <;> cases byte <;> cases signed <;>
          simpa [shape, SubwordMemory.Proofs.rowData, SubwordMemory.importedConstraintsDecoderColumns, Nat.testBit] using flag
      have cell := pooled_subword_cell clockSize inverse accepted clocks image member store selected
      have address := pooled_subword_address hp inverse accepted clocks image wordSetup subwordSetup
        programImage decoded member originalSource.fields query store selected
      apply SubwordMemory.Proofs.local_execution (by omega) inverse core (accepted.active _ member)
        trace.memoryEpoch ordinary originalSource.fields query store byte signed imm rs1 rs2 rd encoding
        selected bounds address cell.2.2 (history_configuration past configuration) ?_ history
      intro cell bounded low member
      exact cell_read_PC (.ram cell.toBitVec)
        (cell_read_nextPC (.ram cell.toBitVec) (romReads cell bounded low member)
          (Word.mk (w 0).val (w 1).val).toBitVec)
        (Word.mk (w 0).val (w 1).val).toBitVec
    have fields := originalSource.fields
    unfold SubwordMemory.decoderFields at fields
    split at fields
    case h_1 => rename_i _ imm rs1 rd encoding; exact operation false true true imm rs1 0 rd encoding
    case h_2 => rename_i _ imm rs1 rd encoding; exact operation false true false imm rs1 0 rd encoding
    case h_3 => rename_i _ imm rs1 rd encoding; exact operation false false true imm rs1 0 rd encoding
    case h_4 => rename_i _ imm rs1 rd encoding; exact operation false false false imm rs1 0 rd encoding
    case h_5 => rename_i _ imm rs2 rs1 encoding; exact operation true true false imm rs1 rs2 0 encoding
    case h_6 => rename_i _ imm rs2 rs1 encoding; exact operation true false false imm rs1 rs2 0 encoding
    case h_7 => cases fields

end Airbender.Trace.Proofs
