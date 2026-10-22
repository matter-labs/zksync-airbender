import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.JumpBranchSlt.Branch
import Airbender.Review.Circuits.JumpBranchSlt.Jump
import Airbender.Proofs.Trace.RowContext
import Airbender.Proofs.Trace.PooledExecution
import Airbender.Proofs.VerifierBoundary

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs

private theorem original_source {p : Nat} [Fact p.Prime]
    {initial : State} {entry : PooledProgramEntry} {w : Nat → ZMod p}
    (source : entry.SourceWith initial pooledDecoderFields)
    (family : entry.data.family = .jumpBranchSlt) (query : decoderQuery w = entry.query) :
    ∃ original : JumpBranchSlt.ProgramEntry, original.SourceWith initial decoderFields ∧
      original.instruction = entry.instruction ∧ decoderQuery w = original.query := by
  obtain original | original | original | original | original := pooled_source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · cases mode : originalEntry.data.family <;>
      simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
  · exact ⟨originalEntry, originalSource, rfl, by simpa only [mapped_query] using query⟩
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

private theorem register_effects {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 32)
    {cells : List Cell} (epoch : Nat) {w : Nat → ZMod p} {rd : BitVec 5}
    (rdColumn : w 7 = (rd.toNat : ZMod p)) (output : Output)
    (outputLo : output.destination.lo = (w 30).val)
    (outputHi : output.destination.hi = (w 31).val)
    {rawBefore rawAfter before : State}
    (history : SailHistory cells (nativeEvents epoch w).reverse rawBefore rawAfter)
    (atState : before = retiredState rawBefore (Word.mk (w 0).val (w 1).val).toBitVec) :
    run (projectedStep (.Regidx rd) output) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState rawAfter output.pc.toBitVec) := by
  have normalized := retired_state_history history (Word.mk (w 0).val (w 1).val).toBitVec
  rw [← atState] at normalized
  have projected := register_history_projection hp epoch
    (first := importedConstraintsMemoryPorts[0]) (second := importedConstraintsMemoryPorts[1])
    (destination := importedConstraintsMemoryPorts[2]) rfl rfl rfl rdColumn output (by
      simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord,
        Nat.unpair_pair, Word.toBitVec, Word.value, outputLo, outputHi]) normalized
  rw [retired_state_overwrite] at projected
  exact projected

set_option backward.isDefEq.respectTransparency false in
theorem pooled_comparison_soundness {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Clock p)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    Comparison.InterfaceAssumptions trace initial cells program →
    Properties.Soundness (Comparison.circuitModel trace initial cells program).relation Comparison.spec := by
  rintro assumptions input output w ⟨⟨accepted, decoded, member⟩, mapping⟩
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  obtain ⟨events, rawBefore, rawAfter, _, _, history, atState⟩ := pooled_row_context
    clockSize inverse accepted assumptions.initialization.clocks assumptions.initialization.image
    assumptions.initialization.distinct assumptions.initialization.aligned programImage decoded mapping.state
  change input.before = retiredState rawBefore (Word.mk (w 0).val (w 1).val).toBitVec at atState
  obtain ⟨leftBound, rightBound, aligned, finalHi⟩ := pooled_control_bounds hp inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image assumptions.wordTable
    assumptions.subwordTable programImage decoded assumptions.codeAligned (VerifierBoundary.Proofs.trace_terminal_bound (by dsimp [limbBase]; omega) accepted assumptions.verifierBoundary) member
  obtain ⟨entry, present, family, query, encoding⟩ := mapping.instruction
  change decoderQuery w = entry.query at query
  obtain ⟨original, source, originalInstruction, query⟩ := original_source
    (run_program_sources programImage entry present) family query
  have encoding := originalInstruction.trans encoding
  cases rs1Index : input.rs1 with | Regidx rs1 =>
    cases rs2Index : input.rs2 with | Regidx rs2 =>
      cases rdIndex : input.rd with | Regidx rd =>
        have pcWord : output.pc = Word.mk (w 16).val (w 17).val :=
          congrArg₂ Word.mk mapping.words.finalPCLo mapping.words.finalPCHi
        have projected := register_effects (by omega) trace.memoryEpoch
          (by simpa only [rdIndex] using mapping.words.rdIndex) output
          mapping.words.outputLo mapping.words.outputHi history atState
        refine ⟨_, ?_, by simpa only [rdIndex] using projected⟩
        cases opcode : input.opcode
        case slt =>
          have normal := local_comparison_execution (by omega) h (accepted.active _ member)
            trace.memoryEpoch source query leftBound rightBound aligned finalHi .slt
            input.encodedImmediate rs1 rs2 rd
            (by simpa only [Comparison.instruction, opcode, rs1Index, rs2Index, rdIndex] using encoding) history
          simpa only [Comparison.execution, Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, opcode, rs1Index, rs2Index, rdIndex,
            ← atState, ← pcWord] using normal
        case slti =>
          have normal := local_comparison_execution (by omega) h (accepted.active _ member)
            trace.memoryEpoch source query leftBound rightBound aligned finalHi .slti
            input.encodedImmediate rs1 rs2 rd
            (by simpa only [Comparison.instruction, opcode, rs1Index, rs2Index, rdIndex] using encoding) history
          simpa only [Comparison.execution, Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, opcode, rs1Index, rs2Index, rdIndex,
            ← atState, ← pcWord] using normal
        case sltu =>
          have normal := local_comparison_execution (by omega) h (accepted.active _ member)
            trace.memoryEpoch source query leftBound rightBound aligned finalHi .sltu
            input.encodedImmediate rs1 rs2 rd
            (by simpa only [Comparison.instruction, opcode, rs1Index, rs2Index, rdIndex] using encoding) history
          simpa only [Comparison.execution, Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, opcode, rs1Index, rs2Index, rdIndex,
            ← atState, ← pcWord] using normal
        case sltiu =>
          have normal := local_comparison_execution (by omega) h (accepted.active _ member)
            trace.memoryEpoch source query leftBound rightBound aligned finalHi .sltiu
            input.encodedImmediate rs1 rs2 rd
            (by simpa only [Comparison.instruction, opcode, rs1Index, rs2Index, rdIndex] using encoding) history
          simpa only [Comparison.execution, Comparison.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, opcode, rs1Index, rs2Index, rdIndex,
            ← atState, ← pcWord] using normal

set_option backward.isDefEq.respectTransparency false in
theorem pooled_branch_soundness {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Clock p)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    Branch.InterfaceAssumptions trace initial cells program →
    Properties.Soundness (Branch.circuitModel trace initial cells program).relation Branch.spec := by
  rintro assumptions input output w ⟨⟨accepted, decoded, member⟩, mapping⟩
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  obtain ⟨events, rawBefore, rawAfter, _, past, history, atState⟩ := pooled_row_context
    clockSize inverse accepted assumptions.initialization.clocks assumptions.initialization.image
    assumptions.initialization.distinct assumptions.initialization.aligned programImage decoded mapping.state
  change input.before = retiredState rawBefore (Word.mk (w 0).val (w 1).val).toBitVec at atState
  obtain ⟨leftBound, rightBound, aligned, finalHi⟩ := pooled_control_bounds hp inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image assumptions.wordTable
    assumptions.subwordTable programImage decoded assumptions.codeAligned (VerifierBoundary.Proofs.trace_terminal_bound (by dsimp [limbBase]; omega) accepted assumptions.verifierBoundary) member
  obtain ⟨entry, present, family, query, encoding⟩ := mapping.instruction
  change decoderQuery w = entry.query at query
  obtain ⟨original, source, originalInstruction, query⟩ := original_source
    (run_program_sources programImage entry present) family query
  have encoding := originalInstruction.trans encoding
  cases rs1Index : input.rs1 with | Regidx rs1 =>
    cases rs2Index : input.rs2 with | Regidx rs2 =>
      have normal := local_branch_execution (by omega) h (accepted.active _ member)
        trace.memoryEpoch source query leftBound rightBound aligned finalHi input.opcode
        input.encodedOffset rs1 rs2 (by simpa only [Branch.instruction, rs1Index, rs2Index] using encoding)
        history past assumptions.isa
      dsimp only at normal
      rw [← atState] at normal
      have pcWord : output.pc = Word.mk (w 16).val (w 17).val :=
        congrArg₂ Word.mk mapping.words.finalPCLo mapping.words.finalPCHi
      rw [← pcWord] at normal
      have rdColumn : w 7 = (0 : ZMod p) := by
        have indices := native_query_indices (by dsimp [limbBase]; omega) query
        have fields := source.fields
        rw [encoding] at fields
        have shape := (Option.some.inj fields).symm
        have index := indices.2.2
        change (w 7).val = original.data.rd.toNat at index
        rw [shape] at index
        simpa using (ZMod.natCast_zmod_val (w 7)).symm.trans
          (congrArg (fun n : Nat => (n : ZMod p)) index)
      have projected := register_effects (by omega) trace.memoryEpoch (rd := 0) (by simpa using rdColumn) output
        mapping.words.outputLo mapping.words.outputHi history atState
      exact ⟨_, by simpa only [Branch.execution, Branch.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, rs1Index, rs2Index] using normal, projected⟩

set_option backward.isDefEq.respectTransparency false in
theorem pooled_jump_soundness {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Clock p)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    (Jump.circuitModel trace initial cells program).SoundnessUnder
      (Jump.InterfaceAssumptions trace initial cells program) Jump.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  have h := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  obtain ⟨events, rawBefore, rawAfter, _, past, history, atState⟩ := pooled_row_context
    clockSize inverse accepted assumptions.initialization.clocks assumptions.initialization.image
    assumptions.initialization.distinct assumptions.initialization.aligned programImage decoded mapping.state
  change input.before = retiredState rawBefore (Word.mk (w 0).val (w 1).val).toBitVec at atState
  obtain ⟨leftBound, _, aligned, finalHi⟩ := pooled_control_bounds hp inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image assumptions.wordTable
    assumptions.subwordTable programImage decoded assumptions.codeAligned (VerifierBoundary.Proofs.trace_terminal_bound (by dsimp [limbBase]; omega) accepted assumptions.verifierBoundary) member
  obtain ⟨entry, present, family, query, encoding⟩ := mapping.instruction
  change decoderQuery w = entry.query at query
  obtain ⟨original, source, originalInstruction, query⟩ := original_source
    (run_program_sources programImage entry present) family query
  have encoding := originalInstruction.trans encoding
  cases rs1Index : input.rs1 with | Regidx rs1 =>
    cases rdIndex : input.rd with | Regidx rd =>
      have pcWord : output.pc = Word.mk (w 16).val (w 17).val :=
        congrArg₂ Word.mk mapping.words.finalPCLo mapping.words.finalPCHi
      have projected := register_effects (by omega) trace.memoryEpoch
        (by simpa only [rdIndex] using mapping.words.rdIndex) output
        mapping.words.outputLo mapping.words.outputHi history atState
      refine ⟨_, ?_, by simpa only [rdIndex] using projected⟩
      cases instruction : input.instruction
      case jal imm =>
        have normal := local_jump_execution (by omega) h (accepted.active _ member)
          trace.memoryEpoch source query leftBound aligned finalHi (.jal imm) rs1 rd
          (by simpa only [Jump.instruction, instruction, rs1Index, rdIndex] using encoding) history past assumptions.isa
          (by simpa only [instruction] using assumptions.landingPad)
        simpa only [Jump.execution, Jump.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, instruction, rs1Index, rdIndex, ← atState, ← pcWord] using normal
      case jalr imm =>
        have normal := local_jump_execution (by omega) h (accepted.active _ member)
          trace.memoryEpoch source query leftBound aligned finalHi (.jalr imm) rs1 rd
          (by simpa only [Jump.instruction, instruction, rs1Index, rdIndex] using encoding) history past assumptions.isa
          (by simpa only [instruction] using assumptions.landingPad)
        simpa only [Jump.execution, Jump.instruction, Reference.RiscV.Sail.registerClause, Option.get_some, instruction, rs1Index, rdIndex, ← atState, ← pcWord] using normal

end Airbender.JumpBranchSlt.Proofs
