import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.Families.MulDiv.Execution
import Airbender.Proofs.MulDiv.Execution
import Airbender.Proofs.Trace.CompositionCore
import Airbender.Proofs.Trace.Terminal

namespace Airbender.MulDiv.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Original Sail clause dispatch from the same local proof; shared by family
    and pooled histories. No separate instruction behavior is defined. -/
theorem local_instruction_execution {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Limb16 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    {initial : State} {cells : List Cell} (epoch : Nat)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (leftBound : (Word.mk (w 20).val (w 21).val).Bounded)
    {before after : State}
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after) :
    ∃ clause, Trace.instructionClause entry.instruction = some clause ∧
      run (normalStep clause)
        (Trace.retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (Trace.retiredState after (Word.mk (w 14).val (w 15).val).toBitVec) := by
  have operation (opcode : Operation) (rs1 rs2 rd : BitVec 5)
      (encoding : entry.instruction = match opcode with
        | .mul => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.Low, .Signed, .Signed⟩)
        | .mulhu => .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.High, .Unsigned, .Unsigned⟩)
        | .divu => .DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, true)
        | .remu => .REM (.Regidx rs2, .Regidx rs1, .Regidx rd, true)) :
      ∃ clause, Trace.instructionClause entry.instruction = some clause ∧
        run (normalStep clause)
          (Trace.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec) =
          .ok SailRV32.Functions.RETIRE_SUCCESS
            (Trace.retiredState after (⟨(w 14).val, (w 15).val⟩ : Word).toBitVec) := by
    have checked := local_row_execution hp inverse h epoch source query leftBound
      opcode rs1 rs2 rd encoding history
    cases opcode <;> dsimp [MulDiv.execution, MulDiv.instruction, Reference.RiscV.Sail.registerClause, Option.get_some] at checked
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
set_option maxHeartbeats 2000000 in
/-- Public decoding supplies the actual clause. Native histories supply its
    operands and preserve the original decoder's public ISA configuration. -/
theorem row_rebased_step {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Limb16 p)
    (clockInverse : SerializedInverse.Clock p)
    {trace : NativeTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program)
    {row : Row p TraceKind} (member : row ∈ trace.rows)
    {before after : State} {events : List MemoryAccess}
    (native : ∀ event ∈ events, event ∈ trace.nativeEvents)
    (past : Trace.SailHistory cells events initial before)
    (history : Trace.SailHistory cells
      (Trace.rowEvents trace.memoryEpoch row).reverse before after) :
    SailStep program (Trace.retiredState before row.start.word.toBitVec)
      (Trace.retiredState after row.finish.word.toBitVec) := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, image⟩ := inputs.programImage
  obtain ⟨entry, present, _, query⟩ := Trace.Proofs.decoder_member (decoded row member)
  have source := Trace.Proofs.run_program_sources image entry present
  have memory := Trace.Proofs.register_history_memory past
    (fun event em => native_register_addresses limbSize decoded (native event em))
  have bytes := read_word_frame (before := initial)
    (after := Trace.retiredState before row.start.word.toBitVec) memory source.bytes
  have fetched := Trace.Proofs.native_query_pc_word limbSize query
  change row.start.word = Word.ofBitVec entry.pc at fetched
  have position : row.start.word.toBitVec = entry.pc := by rw [fetched, Word.ofBitVec_roundtrip]
  have pc : run (SailRV32.Functions.get_arch_pc ()) (Trace.retiredState before row.start.word.toBitVec) =
      .ok entry.pc (Trace.retiredState before row.start.word.toBitVec) := by
    simpa only [position] using Trace.Proofs.retired_state_pc before row.start.word.toBitVec
  have configuration : (Trace.retiredState before row.start.word.toBitVec).regs.get? .misa =
      initial.regs.get? .misa := by
    simpa [Trace.retiredState, Std.ExtDHashMap.get?_insert] using
      (Trace.Proofs.sail_history_control_flow_csrs past).1
  refine ⟨entry, present, ⟨bytes, (decoded_misa_frame _ source.decoded).2 _ configuration,
    source.fields⟩, pc, ?_⟩
  cases row with
  | mk family w =>
    cases family
    have clockField : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
    have h := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
    have bound := (native_value_bounds clockField clockInverse accepted inputs.clocks inputs.image).1
      _ member importedConstraintsMemoryPorts[0] (by simp [Row.ports, importedConstraintsMemoryPorts])
    have left : (Word.mk (w 20).val (w 21).val).Bounded := by
      simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts] using bound
    exact local_instruction_execution hp inverse h trace.memoryEpoch source query left history

set_option backward.isDefEq.respectTransparency false in
/-- Complete instruction traces reuse the shared composition theorem and the
    derived native order/history. Terminal GPR reads are actual Sail reads. -/
theorem native_trace_execution {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Limb16 p)
    (clockInverse : SerializedInverse.Clock p)
    {trace : NativeTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    ∃ after, MulDiv.SailTrace program initial after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (Trace.memoryWord sink.value) after := by
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
      (rows.flatMap fun row => (Trace.rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
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
