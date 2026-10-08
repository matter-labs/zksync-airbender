import Airbender.Proofs.Trace.Composition
import Airbender.Proofs.Trace.OracleConsumption

namespace Airbender.Trace.NonDeterminism.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace.Proofs

theorem clause_standard [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {instruction : SailRV32.instruction} {data : DecoderData}
    (fields : Trace.decoderFields instruction = some data)
    {stream : List (BitVec 32)} {position : Nat}
    {original : SailRV32.SailM SailRV32.ExecutionResult}
    (selected : profileClause .airbender instruction = some original) :
    clause stream position instruction = some (original, position) := by
  unfold clause
  split <;> simp_all [Trace.decoderFields]

/-- The native destination port supplies the entire register update. Stream
    agreement is only the external input boundary, while PC+4 is proved from
    the same imported equations as every other ADD/SUB row. -/
theorem read_row_execution [Fact p.Prime] (hp : ROM.limit < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (initialPC : trace.initial.word.Bounded)
    {w : Nat → ZMod p} (member : (⟨.addSub, w⟩ : Row p) ∈ trace.rows)
    {entry : ProgramEntry} {rd : BitVec 5}
    (data : entry.data = ⟨.addSub, 0, 0, rd, ⟨0, 0⟩, 256, 0⟩)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    {cells : List Cell} {before after : State}
    (history : SailHistory cells
      (rowEvents trace.memoryEpoch (⟨.addSub, w⟩ : Row p)).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (⟨.addSub, w⟩ : Row p).start.word.toBitVec before) :
    run (normalStep (writeResult (.Regidx rd) (Word.ofBitVec (response (⟨.addSub, w⟩ : Row p))))) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState after (⟨.addSub, w⟩ : Row p).finish.word.toBitVec) := by
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at hp ⊢; omega
  have written := (addsub_history_registers limbSize query trace.memoryEpoch history).2
  rw [data] at written
  change run (SailRV32.Functions.wX_bits (.Regidx rd)
    (Word.mk (w 33).val (w 34).val).toBitVec) before = .ok () after at written
  let value := response (⟨.addSub, w⟩ : Row p)
  change run (SailRV32.Functions.wX_bits (.Regidx rd) value) before = .ok () after at written
  have next := row_pc_successor (by dsimp [ROM.limit, timestampBase] at hp ⊢; omega)
    inverse accepted initialPC member
  have prepared := cell_write_control .nextPC (.inr rfl)
    ((⟨.addSub, w⟩ : Row p).start.word.toBitVec + 4) (.register rd) value written
  have executed := run_bind_of_ok (SailRV32.Functions.wX_bits (.Regidx rd) value)
    (fun _ => (pure SailRV32.Functions.RETIRE_SUCCESS : SailRV32.SailM _)) _ _ _ prepared
  have checked := normal_step_native (writeResult (.Regidx rd) (Word.ofBitVec value)) pc
    (by simpa only [writeResult, Word.ofBitVec_roundtrip, run_return] using executed)
  rw [← next] at checked
  exact checked

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
theorem instruction_step {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : ROM.limit < p) (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    {initial : State} {cells : List Cell}
    (image : initialImage initial cells = some trace.initialMemory)
    (setup : trace.rom = ROM.table cells trace.initialMemory)
    (registers : ∀ index, Cell.register index ∈ cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address)
    (configuration : FlatMemoryConfiguration initial) (initialPC : trace.initial.word.Bounded)
    {row : Row p} (member : row ∈ trace.rows) {entry : ProgramEntry}
    (fields : NonDeterminism.decoderFields entry.instruction = some entry.data)
    (family : entry.data.family = row.family) (query : row.decoderQuery = entry.query)
    {stream : List (BitVec 32)} {position : Nat}
    (port : isRead row = true → stream[position]? = some (response row))
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : SailHistory cells events initial before)
    (history : SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after)
    (pc : run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before) :
    ∃ original, clause stream position entry.instruction =
      some (original, position + if isRead row then 1 else 0) ∧
      run (normalStep original) before =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) := by
  have limbSize : limbBase < p := by dsimp [ROM.limit, limbBase] at hp ⊢; omega
  have flag := read_flag limbSize accepted member (field_bounds fields).2 query
  rcases fields_cases fields with standard | ⟨rd, nonzero, encoding, data⟩ |
    ⟨rs1, nonzero, encoding, data⟩
  · have small := (decoder_field_bounds standard).2
    have bit : entry.data.mask.testBit 8 = false := by
      have division : entry.data.mask / 256 = 0 := Nat.div_eq_of_lt (by omega)
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, division]
    have unread : isRead row = false := by
      rw [flag]
      cases row.family <;> simp [bit]
    obtain ⟨original, selected, checked⟩ := row_instruction_step .airbender hp inverse
      accepted boundary image setup registers aligned ordinary configuration initialPC
      member standard family query (by intro impossible; cases impossible) native past history pc
    exact ⟨original, by simpa [unread] using clause_standard standard selected, checked⟩
  · have selected : row.family = .addSub := by rw [← family, data]
    cases row with
    | mk current w =>
      change current = .addSub at selected
      subst current
      have read : isRead (⟨.addSub, w⟩ : Row p) = true := by
        rw [flag, data]
        norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have supplied := port read
      refine ⟨writeResult (.Regidx rd) (Word.ofBitVec (response (⟨.addSub, w⟩ : Row p))), ?_, ?_⟩
      · rw [encoding]
        simp [clause, supplied, read, bind, Option.bind]
        exact nonzero
      · exact read_row_execution hp inverse accepted initialPC member data query history pc
  · have selected : row.family = .addSub := by rw [← family, data]
    cases row with
    | mk current w =>
      change current = .addSub at selected
      subst current
      have unread : isRead (⟨.addSub, w⟩ : Row p) = false := by
        rw [flag, data]
        norm_num [Nat.testBit, Nat.shiftRight_eq_div_pow]
      let nop : ProgramEntry := { entry with instruction := .ITYPE (0, .Regidx 0, .Regidx 0, .ADDI) }
      have nopFields : Trace.decoderFields nop.instruction = some nop.data := by
        change some ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ = some entry.data
        rw [data]
      obtain ⟨original, selected, checked⟩ := row_instruction_step .airbender hp inverse
        accepted boundary image setup registers aligned ordinary configuration initialPC
        member nopFields (entry := nop) family query (by intro impossible; cases impossible)
        native past history pc
      change some (SailRV32.Functions.execute_ITYPE 0 (.Regidx 0) (.Regidx 0) .ADDI) =
        some original at selected
      have nopClause : SailRV32.Functions.execute_ITYPE 0 (.Regidx 0) (.Regidx 0) .ADDI =
          (pure SailRV32.Functions.RETIRE_SUCCESS : SailRV32.SailM _) := by rfl
      have same := (Option.some.inj selected).symm.trans nopClause
      rw [same] at checked
      refine ⟨pure SailRV32.Functions.RETIRE_SUCCESS, ?_, checked⟩
      rw [encoding]
      simp [clause, unread]
      exact nonzero

end Airbender.Trace.NonDeterminism.Proofs
