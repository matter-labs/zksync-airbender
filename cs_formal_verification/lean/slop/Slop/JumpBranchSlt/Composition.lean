import Slop.Sail.Configured
import Human.Trace.Families.JumpBranchSlt.Execution
import Slop.JumpBranchSlt.Execution
import Slop.JumpBranchSlt.BranchExecution
import Slop.JumpBranchSlt.ComparisonExecution
import Slop.Trace.CompositionCore
import Slop.Trace.Terminal

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Actual Sail clause dispatch is shared by family and pooled histories. -/
theorem local_instruction_execution {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (active : w 4 = 1) {initial : State} {cells : List Cell} (epoch : Nat)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (leftBound : (Word.mk (w 22).val (w 23).val).Bounded)
    (rightBound : (Word.mk (w 26).val (w 27).val).Bounded)
    (initialAligned : (w 0).val % 4 = 0) (finalHiBound : (w 17).val < limbBase)
    {before after : State} {events : List MemoryAccess}
    (history : Trace.SailHistory cells (nativeEvents epoch w).reverse before after)
    (past : Trace.SailHistory cells events initial before)
    (isa : ∃ value, initial.regs.get? .misa = some value)
    (configuration : initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    ∃ clause, Trace.instructionClause entry.instruction = some clause ∧
      run (normalStep clause) (Trace.retiredState before (Word.mk (w 0).val (w 1).val).toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS
          (Trace.retiredState after (Word.mk (w 16).val (w 17).val).toBitVec) := by
  have comparison (opcode : Comparison.Opcode) (imm : BitVec 12) (rs1 rs2 rd : BitVec 5)
      (encoding : entry.instruction = match opcode with
        | .slt => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLT)
        | .slti => .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTI)
        | .sltu => .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU)
        | .sltiu => .ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU)) :
      ∃ clause, Trace.instructionClause entry.instruction = some clause ∧
        run (normalStep clause) (Trace.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec) =
          .ok SailRV32.Functions.RETIRE_SUCCESS
            (Trace.retiredState after (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec) := by
    have checked := local_comparison_execution hp h active epoch source query leftBound rightBound
      initialAligned finalHiBound opcode imm rs1 rs2 rd encoding history
    cases opcode <;> dsimp [Comparison.execution, Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some] at checked
    all_goals refine ⟨_, ?_, checked⟩; rw [encoding]; rfl
  have jump (instruction : Jump.Instruction) (rs1 rd : BitVec 5)
      (encoding : entry.instruction = match instruction with
        | .jal imm => .JAL (imm, .Regidx rd)
        | .jalr imm => .JALR (imm, .Regidx rs1, .Regidx rd)) :
      ∃ clause, Trace.instructionClause entry.instruction = some clause ∧
        run (normalStep clause) (Trace.retiredState before (⟨(w 0).val, (w 1).val⟩ : Word).toBitVec) =
          .ok SailRV32.Functions.RETIRE_SUCCESS
            (Trace.retiredState after (⟨(w 16).val, (w 17).val⟩ : Word).toBitVec) := by
    have checked := local_jump_execution hp h active epoch source query leftBound initialAligned finalHiBound instruction rs1 rd encoding history past
      isa (fun _ => configuration)
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
    · exact local_branch_execution hp h active epoch source query leftBound rightBound
        initialAligned finalHiBound opcode imm rs1 rs2 encoding
        history past isa
  case h_6 => rename_i _ imm rd encoding; exact jump (.jal imm) 0 rd encoding
  case h_7 => rename_i _ imm rs1 rd encoding; exact jump (.jalr imm) rs1 rd encoding
  case h_8 => cases fields


theorem row_rebased_step {p : Nat} [Fact p.Prime]
    (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
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
  have source := Trace.Proofs.program_sources image entry present
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
  refine ⟨entry, present, ⟨bytes, source.decoded,
    source.fields⟩, pc, ?_⟩
  cases row with
  | mk family w =>
    cases family
    have h := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
    have bounds := (native_value_bounds hp inverse accepted inputs.clocks inputs.image image decoded).1 _ member
    have left := bounds importedConstraintsMemoryPorts[0]
      (by simp [Row.ports, importedConstraintsMemoryPorts])
    have right := bounds importedConstraintsMemoryPorts[1]
      (by simp [Row.ports, importedConstraintsMemoryPorts])
    have leftBound : (Word.mk (w 22).val (w 23).val).Bounded := by
      simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts] using left
    have rightBound : (Word.mk (w 26).val (w 27).val).Bounded := by
      simpa [Trace.Proofs.read_word, importedConstraintsMemoryPorts] using right
    have finalHi := (trace_pc_bounds limbSize accepted decoded inputs.terminalCanonical _ member).2.2
    have aligned := ((trace_pc_alignment hp accepted inputs.initialAligned).1 _ member).1
    exact local_instruction_execution hp h (accepted.active _ member) trace.memoryEpoch source query
      leftBound rightBound aligned finalHi history past inputs.configuration.isa
      ⟨inputs.configuration.privilege, inputs.configuration.landingPad⟩

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
        cell.read after = .ok (Trace.memoryWord sink.value) after := by
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
      (rows.flatMap fun row => (Trace.rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [Trace.Proofs.native_events_projection clockSize inverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have execution := Trace.Proofs.compose_native_rows initialRead
    (fun row member {before after events} native past current =>
      row_rebased_step hp inverse inputs accepted decoded member native past current)
    rows trace.terminal (fun row present => permutation.mem_iff.mp present)
    (fun event present => eventPermutation.mem_iff.mp present) chain nativeHistory
  exact Trace.Proofs.native_trace_postconditions clockSize inverse accepted inputs.clocks
    inputs.image inputs.distinct initialRead consistent chain nativeHistory matchedState execution

end Airbender.JumpBranchSlt.Proofs
