import Human.Trace.Families.SubwordMemory.Execution
import Slop.SubwordMemory.Execution
import Slop.Trace.CompositionCore

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem row_ram_step {p : Nat} [Fact p.Prime]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : RAMInputs trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program)
    {row : Row p TraceKind} (member : row ∈ trace.rows)
    {before after : State} {events : List _root_.MemoryAccess}
    (past : Trace.SailHistory cells events initial before)
    (history : Trace.SailHistory cells
      (Trace.rowEvents trace.memoryEpoch row).reverse before after) :
    SailStep program (Trace.retiredState before row.start.word.toBitVec)
      (Trace.retiredState after row.finish.word.toBitVec) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, image⟩ := inputs.programImage
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member (decoded row member)
  have source := Trace.Proofs.run_program_sources image entry present
  have bytes := Trace.Proofs.history_code_frame_of_domain past inputs.ramDomain
    entry.pc (inputs.code entry present).1 (inputs.code entry present).2 source.bytes
  have fetched := Trace.Proofs.native_query_pc_word limbSize query
  change row.start.word = Word.ofBitVec entry.pc at fetched
  have position : row.start.word.toBitVec = entry.pc := by rw [fetched, Word.ofBitVec_roundtrip]
  have pc : run (SailRV32.Functions.get_arch_pc ())
      (Trace.retiredState before row.start.word.toBitVec) =
      .ok entry.pc (Trace.retiredState before row.start.word.toBitVec) := by
    simpa only [position] using Trace.Proofs.retired_state_pc before row.start.word.toBitVec
  have configuration : ConfigSame initial (Trace.retiredState before row.start.word.toBitVec) :=
    ((Trace.Proofs.sail_history_config_same past).insert (key := .nextPC) rfl _).insert (key := .PC) rfl _
  refine ⟨entry, present, ⟨Trace.Proofs.cell_read_PC (.ram entry.pc)
    (Trace.Proofs.cell_read_nextPC (.ram entry.pc) bytes row.start.word.toBitVec) row.start.word.toBitVec,
    (decoded_misa_frame _ source.decoded).2 _ configuration, source.fields⟩, pc, ?_⟩
  obtain ⟨values, setup⟩ := inputs.setup
  cases row with
  | mk family w =>
    cases family
    have operation (store byte signed : Bool) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
        (encoding : entry.instruction = rowInstruction store byte signed imm rs1 rs2 rd) :=
      row_ram_execution hp inverse accepted inputs.clocks inputs.image setup inputs.ramDomain
        inputs.ordinary inputs.configuration member source.fields query
        store byte signed imm rs1 rs2 rd encoding past history
    have fields := source.fields
    unfold decoderFields at fields
    split at fields
    case h_1 => rename_i _ imm rs1 rd encoding; exact operation false true true imm rs1 0 rd encoding
    case h_2 => rename_i _ imm rs1 rd encoding; exact operation false true false imm rs1 0 rd encoding
    case h_3 => rename_i _ imm rs1 rd encoding; exact operation false false true imm rs1 0 rd encoding
    case h_4 => rename_i _ imm rs1 rd encoding; exact operation false false false imm rs1 0 rd encoding
    case h_5 => rename_i _ imm rs2 rs1 encoding; exact operation true true false imm rs1 rs2 0 encoding
    case h_6 => rename_i _ imm rs2 rs1 encoding; exact operation true false false imm rs1 rs2 0 encoding
    case h_7 => cases fields

set_option backward.isDefEq.respectTransparency false in
/-- Complete RAM subword traces reuse global latest-write/read consistency,
    native clocks and the same Sail composition used by the other families. -/
theorem ram_trace_execution {p : Nat} [Fact p.Prime]
    (hp : 33554432 < p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : RAMInputs trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    ∃ after, SailTrace program initial after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (Trace.memoryWord sink.value) after := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨timestamp, bound⟩ := inputs.initialPC
  obtain ⟨addresses, programBound⟩ := inputs.programImage
  have initialRead := Trace.Proofs.initial_state_pc limbSize bound
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    decoded_native_history clockSize inverse accepted inputs.clocks inputs.image inputs.distinct inputs.aligned
      programBound decoded
  have chain := Trace.Proofs.ordered_row_boundaries clockSize inverse accepted inputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (Trace.rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [Trace.Proofs.native_events_projection clockSize inverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := Trace.Proofs.compose_native_rows initialRead
    (fun row member {before after events} _ past current =>
      row_ram_step hp inverse inputs accepted decoded member past current)
    rows trace.terminal (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  exact Trace.Proofs.native_trace_postconditions clockSize inverse accepted inputs.clocks
    inputs.image inputs.distinct initialRead consistent chain nativeHistory matchedState execution

end Airbender.SubwordMemory.Proofs
