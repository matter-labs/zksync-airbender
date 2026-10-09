import Airbender.Review.JumpBranchSlt.Execution
import Airbender.Proofs.JumpBranchSlt.Execution
import Airbender.Proofs.JumpBranchSlt.BranchExecution
import Airbender.Proofs.JumpBranchSlt.ComparisonExecution
import Airbender.Proofs.Trace.CompositionCore
import Airbender.Proofs.Trace.Terminal

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Dispatch only instructions extracted by the actual Sail decoder. Each
    family mode derives its local interfaces and reaches the native after-state. -/
theorem row_rebased_step {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
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
  have source := Trace.Proofs.program_sources image entry present
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
  refine ⟨entry, present, ⟨bytes, (decoded_misa_frame _ source.decoded).2 _
    (by simpa [Trace.Proofs.retiredState, Std.ExtDHashMap.get?_insert] using
      (Trace.Proofs.sail_history_control_flow_csrs past).1), source.fields⟩, pc, ?_⟩
  cases row with
  | mk family w =>
    cases family
    have comparison (opcode : Comparison.Opcode) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
        (encoding : entry.instruction = match opcode with
          | .slt => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLT)
          | .slti => .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTI)
          | .sltu => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU)
          | .sltiu => .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU)) :
        ∃ clause, Trace.instructionClause entry.instruction = some clause ∧
          run (normalStep clause) (Trace.Proofs.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec) =
            .ok SailRV32.Functions.RETIRE_SUCCESS
              (Trace.Proofs.retiredState after (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec) := by
      have checked := comparison_rebased_step hp inverse accepted inputs.clocks inputs.image image decoded
        inputs.terminalCanonical inputs.initialAligned member present query opcode imm rs1 rs2 rd encoding history
      cases opcode <;> dsimp [Comparison.execution] at checked
      all_goals refine ⟨_, ?_, checked⟩; rw [encoding]; rfl
    have jump (instruction : Jump.Instruction) (rs1 rd : BitVec 5)
        (encoding : entry.instruction = match instruction with
          | .jal imm => .JAL (imm, .Regidx rd)
          | .jalr imm => .JALR (imm, .Regidx rs1, .Regidx rd)) :
        ∃ clause, Trace.instructionClause entry.instruction = some clause ∧
          run (normalStep clause) (Trace.Proofs.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec) =
            .ok SailRV32.Functions.RETIRE_SUCCESS
              (Trace.Proofs.retiredState after (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec) := by
      have checked := jump_rebased_step hp inverse accepted inputs.clocks inputs.image image decoded
        inputs.terminalCanonical inputs.initialAligned member present query instruction rs1 rd encoding history past
        inputs.misa (fun _ => inputs.indirect)
      cases instruction <;> dsimp at checked
      all_goals refine ⟨_, ?_, checked⟩; rw [encoding]; rfl
    have fields := source.fields
    unfold decoderFields at fields
    split at fields
    case h_1 => rename_i _ rs2 rs1 rd encoding; exact comparison .slt 0 rs1 rs2 rd encoding
    case h_2 => rename_i _ rs2 rs1 rd encoding; exact comparison .sltu 0 rs1 rs2 rd encoding
    case h_3 => rename_i _ imm rs1 rd encoding; exact comparison .slti imm rs1 0 rd encoding
    case h_4 => rename_i _ imm rs1 rd encoding; exact comparison .sltiu imm rs1 0 rd encoding
    case h_5 =>
      rename_i _ imm rs2 rs1 opcode encoding
      refine ⟨SailRV32.Functions.execute_BTYPE imm (.Regidx rs2) (.Regidx rs1) opcode, ?_, ?_⟩
      · rw [encoding]; rfl
      · exact branch_rebased_step hp inverse accepted inputs.clocks inputs.image image decoded
          inputs.terminalCanonical inputs.initialAligned member present query opcode imm rs1 rs2 encoding
          history past inputs.misa
    case h_6 => rename_i _ imm rd encoding; exact jump (.jal imm) 0 rd encoding
    case h_7 => rename_i _ imm rs1 rd encoding; exact jump (.jalr imm) rs1 rd encoding
    case h_8 => cases fields

set_option backward.isDefEq.respectTransparency false in
/-- Complete instruction traces reuse the shared composition theorem and the
    derived native order/history. Terminal GPR reads are actual Sail reads. -/
theorem native_trace_execution {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : NativeTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    (inputs : ExecutionBoundary trace initial cells program)
    (accepted : Accepted trace) (decoded : Decoded trace program) :
    ∃ after, JumpBranchSlt.SailTrace program initial after ∧
      run (SailRV32.Functions.get_arch_pc ()) after = .ok trace.terminal.word.toBitVec after ∧
      ∀ sink ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = sink.address ∧
        cell.read after = .ok (Trace.Proofs.memoryWord sink.value) after := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase] at *; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨timestamp, bound⟩ := inputs.initialPC
  obtain ⟨addresses, programBound⟩ := inputs.programImage
  have initialRead := Trace.Proofs.initial_state_pc limbSize bound
  obtain ⟨history, rows, nativeAfter, consistent, permutation, ordered, nativeHistory, matchedState⟩ :=
    decoded_native_history clockSize inverse accepted inputs.clocks inputs.image inputs.distinct inputs.aligned
      programBound decoded
  have chain := Trace.Proofs.ordered_row_boundaries clockSize inverse accepted inputs.clocks permutation ordered
  have eventPermutation :
      (rows.flatMap fun row => (Trace.Proofs.rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [Trace.Proofs.native_events_projection clockSize inverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := Trace.Proofs.compose_native_rows initialRead
    (fun row member {before after events} native past current =>
      row_rebased_step hp inverse inputs accepted decoded member native past current)
    rows trace.terminal (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  let final := match rows with
    | [] => nativeAfter
    | _ :: _ => Trace.Proofs.retiredState nativeAfter trace.terminal.word.toBitVec
  have pc : run (SailRV32.Functions.get_arch_pc ()) final = .ok trace.terminal.word.toBitVec final := by
    cases rows with
    | nil =>
      have same : trace.terminal = trace.initial := by simpa using chain
      rw [same]
      exact Trace.Proofs.sail_history_pc_read nativeHistory initialRead
    | cons _ _ => exact Trace.Proofs.retired_state_pc nativeAfter trace.terminal.word.toBitVec
  have realized : Trace.Proofs.SailStateMatches cells history final := by
    cases rows with
    | nil => exact matchedState
    | cons _ _ =>
      exact Trace.Proofs.matches_control
        (Trace.Proofs.matches_control matchedState .nextPC (.inr rfl) trace.terminal.word.toBitVec)
        .PC (.inl rfl) trace.terminal.word.toBitVec
  refine ⟨final, ?_, pc, Trace.Proofs.terminal_sail_reads clockSize inverse accepted inputs.clocks
    inputs.image inputs.distinct consistent realized⟩
  cases rows <;> exact execution

end Airbender.JumpBranchSlt.Proofs
