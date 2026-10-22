import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.SubwordMemory.Model
import Airbender.Proofs.Trace.RowContext
import Airbender.Proofs.Trace.PooledSubword

namespace Airbender.SubwordMemory.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Reuse pooled subword execution, containing-cell equations and native effects.
    All operand bounds, reads and Sail access transport come from shared history. -/
theorem pooled_row_soundness {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : FieldCapacity.NativeWordCapacity p) (inverse : SerializedInverse.Clock p)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec := by
  rintro assumptions input output w ⟨⟨accepted, decoded, member⟩, mapping⟩
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom.subwordMemory) importedConstraintsTimestampLookups)
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  obtain ⟨events, rawBefore, rawAfter, native, past, history, atState⟩ := pooled_row_context
    clockSize inverse accepted assumptions.initialization.clocks assumptions.initialization.image
    assumptions.initialization.distinct assumptions.initialization.aligned programImage decoded mapping.state
  change input.before = retiredState rawBefore (Word.mk (w 0).val (w 1).val).toBitVec at atState
  have normalized := retired_state_history history (Word.mk (w 0).val (w 1).val).toBitVec
  rw [← atState] at normalized
  obtain ⟨entry, present, family, query, encoding⟩ := mapping.instruction
  obtain ⟨clause, clauseBound, normal⟩ := pooled_subword_execution hp inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image assumptions.wordTable
    assumptions.subwordTable assumptions.initialization.aligned assumptions.ordinary
    assumptions.configuration programImage decoded member present family query native past history
  have clauseMatches : instructionClause entry.instruction = some (execution input) := by
    rw [encoding]
    cases mode : input.store <;> cases width : input.byte <;>
      simp only [mode, width, execution, instruction, instructionClause, Bool.false_eq_true, if_false, if_true, Option.get_some]
  have same := Option.some.inj (clauseBound.symm.trans clauseMatches)
  rw [same, ← atState] at normal
  have pcWord : output.pc = Word.mk (w 13).val (w 14).val :=
    congrArg₂ Word.mk mapping.words.finalPCLo mapping.words.finalPCHi
  have sourceWord : input.source = Word.mk (w 19).val (w 20).val :=
    congrArg₂ Word.mk mapping.words.sourceLo mapping.words.sourceHi
  have immediateWord : input.immediate = Word.mk (w 8).val (w 9).val :=
    congrArg₂ Word.mk mapping.words.immediateLo mapping.words.immediateHi
  have cellWord : output.cell =
      Word.mk (if input.store then w 27 else w 21).val (if input.store then w 28 else w 22).val :=
    congrArg₂ Word.mk mapping.words.cellLo mapping.words.cellHi
  have dataValue : memoryWord (importedConstraintsMemoryPorts[2].writeCode w) = output.data.toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord,
      Nat.unpair_pair, Word.toBitVec, Word.value, mapping.words.outputLo, mapping.words.outputHi]
  rw [← pcWord] at normal
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
    change decoderQuery w = originalEntry.query at query
    change originalEntry.instruction = _ at encoding
    cases sourceIndex : input.rs1 with | Regidx rs1 =>
      cases secondIndex : input.rs2 with | Regidx rs2 =>
        cases destinationIndex : input.rd with | Regidx rd =>
          have shape := row_decoder_shape input.store input.byte input.signed input.encodedImmediate rs1 rs2 rd
            (by simpa only [instruction, rowInstruction, sourceIndex, secondIndex, destinationIndex] using encoding)
            originalSource.fields
          have flags := decoder_selectors limbSize core (decoder_field_bounds originalSource.fields).2.1 query
          have selected : w 10 = if input.store then 1 else 0 := by
            have flag := flags 0
            cases mode : input.store <;> cases width : input.byte <;> cases sign : input.signed <;>
              simpa [shape, rowData, importedConstraintsDecoderColumns, Nat.testBit, mode, width, sign] using flag
          have address := pooled_subword_address hp inverse accepted assumptions.initialization.clocks
            assumptions.initialization.image assumptions.wordTable assumptions.subwordTable
            programImage decoded member originalSource.fields query input.store selected
          have addressFor : output.cell.toBitVec.toNat =
              (input.source.toBitVec + input.immediate.toBitVec).toNat / 4 * 4 := by
            rw [cellWord, sourceWord, immediateWord, ← address.2.2.2.1]
            exact (aligned_cell_index address.1 address.2.1 address.2.2.1).symm
          refine ⟨addressFor, ?_⟩
          cases mode : input.store
          · simp only [Bool.false_eq_true, if_false]
            have select : w 10 = 0 := by simpa only [mode, Bool.false_eq_true, if_false] using selected
            have written := destination_write limbSize trace.memoryEpoch core select query normalized
            have atRD : originalEntry.data.rd = rd := by
              simp only [shape, rowData, mode, Bool.false_eq_true, if_false]
            rw [atRD, dataValue] at written
            have projected := projected_step_of_write rd ⟨output.data, output.pc⟩ written
            rw [retired_state_overwrite] at projected
            exact ⟨_, normal, by simpa only [destinationIndex] using projected⟩
          · simp only [if_true]
            have select : w 10 = 1 := by simpa only [mode, if_true] using selected
            have cell := pooled_subword_cell clockSize inverse accepted assumptions.initialization.clocks
              assumptions.initialization.image member true select
            have written := native_history_write trace.memoryEpoch rfl rfl rfl normalized
              (ports := importedConstraintsMemoryPorts) (port := importedConstraintsMemoryPorts[2]) rfl cell.2.2
            have atCell : output.cell = Word.mk (w 27).val (w 28).val := by
              simpa only [mode, if_true] using cellWord
            have location : (importedConstraintsMemoryPorts[2].address.word w).toBitVec = output.cell.toBitVec := by
              change (Word.mk (w 27).val (w 28).val).toBitVec = output.cell.toBitVec
              rw [← atCell]
            rw [dataValue] at written
            change run (Sail.writeMemory (size := 4) (importedConstraintsMemoryPorts[2].address.word w).toBitVec
              output.data.toBitVec) input.before = .ok () _ at written
            rw [location] at written
            have projected := projected_step_of_cell_write (.ram output.cell.toBitVec) output.data.toBitVec output.pc written
            rw [retired_state_overwrite] at projected
            exact ⟨_, normal, projected⟩

end Airbender.SubwordMemory.Proofs
