import Airbender.Review.MulDiv.Execution
import Airbender.Proofs.MulDiv.Execution
import Airbender.Proofs.Trace.CompositionCore
import Airbender.Proofs.Trace.Terminal

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Public decoding supplies the actual clause. Native histories supply its
    operands and preserve the original decoder's public ISA configuration. -/
theorem row_rebased_step {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program)
    {row : Row p TraceKind} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : Trace.Proofs.SailHistory cells events initial before)
    (history : Trace.Proofs.SailHistory cells
      (Trace.Proofs.rowEvents trace.memoryEpoch row).reverse before after) :
    SailStep program (Trace.Proofs.retiredState before row.start.word.toBitVec)
      (Trace.Proofs.retiredState after row.finish.word.toBitVec) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, image⟩ := inputs.programImage
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member (decoded row member)
  have source := Trace.Proofs.run_program_sources image entry present
  have memory := Trace.Proofs.register_history_memory past
    (fun event em => native_register_addresses limbSize decoded (native event em))
  have bytes := read_word_frame (before := initial)
    (after := Trace.Proofs.retiredState before row.start.word.toBitVec) memory source.bytes
  have fetched := Trace.Proofs.native_query_pc_word limbSize query
  change row.start.word = Word.ofBitVec entry.pc at fetched
  have position : row.start.word.toBitVec = entry.pc := by rw [fetched, Word.ofBitVec_roundtrip]
  have pc : run (SailRV32.Functions.get_arch_pc ()) (Trace.Proofs.retiredState before row.start.word.toBitVec) =
      .ok entry.pc (Trace.Proofs.retiredState before row.start.word.toBitVec) := by
    simpa only [position] using Trace.Proofs.retired_state_pc before row.start.word.toBitVec
  have configuration : (Trace.Proofs.retiredState before row.start.word.toBitVec).regs.get? .misa =
      initial.regs.get? .misa := by
    simpa [Trace.Proofs.retiredState, Std.ExtDHashMap.get?_insert] using
      (Trace.Proofs.sail_history_control_flow_csrs past).1
  refine ⟨entry, present, ⟨bytes, (decoded_misa_frame _ source.decoded).2 _ configuration,
    source.fields⟩, pc, ?_⟩
  cases row with
  | mk family w =>
    cases family
    have operation (opcode : Operation) (rs1 rs2 rd : BitVec 5)
        (encoding : entry.instruction = match opcode with
          | .mul => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.Low, .Signed, .Signed⟩)
          | .mulhu => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.High, .Unsigned, .Unsigned⟩)
          | .divu => .DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, true)
          | .remu => .REM (.Regidx rs2, .Regidx rs1, .Regidx rd, true)) :
        ∃ clause, Trace.instructionClause entry.instruction = some clause ∧
          run (normalStep clause)
            (Trace.Proofs.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec) =
            .ok SailRV32.Functions.RETIRE_SUCCESS
              (Trace.Proofs.retiredState after (⟨(w 14).val, (w 15).val⟩ : Word).toBitVec) := by
      have checked := row_rebased_execution hp inverse clockInverse accepted inputs.clocks
        inputs.image image decoded member present query opcode rs1 rs2 rd encoding history
      cases opcode <;> dsimp [MulDiv.execution] at checked
      all_goals refine ⟨_, ?_, checked⟩; rw [encoding]; rfl
    have fields := source.fields
    unfold decoderFields at fields
    split at fields
    case h_1 => rename_i _ rs2 rs1 rd encoding; exact operation .mul rs1 rs2 rd encoding
    case h_2 => rename_i _ rs2 rs1 rd encoding; exact operation .mulhu rs1 rs2 rd encoding
    case h_3 => rename_i _ rs2 rs1 rd encoding; exact operation .divu rs1 rs2 rd encoding
    case h_4 => rename_i _ rs2 rs1 rd encoding; exact operation .remu rs1 rs2 rd encoding
    case h_5 => cases fields

set_option backward.isDefEq.respectTransparency false in
/-- Complete instruction traces reuse the shared composition theorem and the
    derived native order/history. Terminal GPR reads are actual Sail reads. -/
theorem native_trace_execution {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    ∃ after, MulDiv.SailTrace program initial after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (Trace.Proofs.memoryWord sink.value) after := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase] at *; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨timestamp, bound⟩ := inputs.initialPC
  obtain ⟨addresses, programBound⟩ := inputs.programImage
  have initialRead := Trace.Proofs.initial_state_pc limbSize bound
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    decoded_native_history clockSize clockInverse accepted inputs.clocks inputs.image inputs.distinct inputs.aligned
      programBound decoded
  have chain := Trace.Proofs.ordered_row_boundaries clockSize clockInverse accepted inputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (Trace.Proofs.rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [Trace.Proofs.native_events_projection clockSize clockInverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := Trace.Proofs.compose_native_rows initialRead
    (fun row member {before after events} native past current =>
      row_rebased_step hp inverse clockInverse inputs accepted decoded member native past current)
    rows trace.terminal (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  exact Trace.Proofs.native_trace_postconditions clockSize clockInverse accepted inputs.clocks
    inputs.image inputs.distinct initialRead consistent chain nativeHistory matchedState execution

end Airbender.MulDiv.Proofs
