import Airbender.Review.WordMemory.Model
import Airbender.Proofs.Trace.RowContext
import Airbender.Proofs.Trace.PooledMemory

namespace Airbender.WordMemory.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
open _root_.Sail.ArchSem

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Reuse pooled LW/SW execution and native transfer proofs at this row's
    represented position. No operand bound, read value or access result is assumed. -/
theorem trace_soundness {p : Nat} [Fact p.Prime] [MemoryPlatform SailRV32.exception]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation spec := by
  rintro assumptions input output w ⟨⟨accepted, decoded, member⟩, mapping⟩
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom.wordMemory) importedConstraintsTimestampLookups)
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  obtain ⟨events, rawBefore, rawAfter, native, past, history, atState⟩ := pooled_row_context
    clockSize inverse accepted assumptions.initialization.clocks assumptions.initialization.image
    assumptions.initialization.distinct assumptions.initialization.aligned
    programImage decoded mapping.state
  have normalized := retired_state_history history (Word.mk (w 0).val (w 1).val).toBitVec
  change SailHistory cells _ (retiredState rawBefore (Word.mk (w 0).val (w 1).val).toBitVec) _ at normalized
  change input.before = retiredState rawBefore (Word.mk (w 0).val (w 1).val).toBitVec at atState
  rw [← atState] at normalized
  obtain ⟨entry, present, family, query, encoding⟩ := mapping.instruction
  obtain ⟨clause, clauseBound, normal⟩ := pooled_word_execution hp inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image assumptions.wordTable
    assumptions.subwordTable assumptions.initialization.aligned assumptions.ordinary
    assumptions.configuration programImage decoded member present family query native past history
  have clauseMatches : instructionClause entry.instruction = some (execution input) := by
    rw [encoding]
    cases mode : input.store <;>
      simp only [mode, execution, instruction, instructionClause, Bool.false_eq_true, if_false, if_true, Option.get_some]
  have sameClause := Option.some.inj (clauseBound.symm.trans clauseMatches)
  rw [sameClause, ← atState] at normal
  have sourceWord : input.source = Word.mk (w 17).val (w 18).val :=
    congrArg₂ Word.mk mapping.words.sourceLo mapping.words.sourceHi
  have immediateWord : input.immediate = Word.mk (w 8).val (w 9).val :=
    congrArg₂ Word.mk mapping.words.immediateLo mapping.words.immediateHi
  have addressWord : output.address =
      Word.mk (w (if input.store then 25 else 19)).val (w (if input.store then 26 else 20)).val :=
    congrArg₂ Word.mk mapping.words.addressLo mapping.words.addressHi
  have dataWord : output.data = Word.mk (w 31).val (w 32).val :=
    congrArg₂ Word.mk mapping.words.outputLo mapping.words.outputHi
  have pcWord : output.pc = Word.mk (w 11).val (w 12).val :=
    congrArg₂ Word.mk mapping.words.finalPCLo mapping.words.finalPCHi
  rw [← pcWord] at normal
  have addressFor (selected : w 10 = if input.store then 1 else 0) :
      output.address.toBitVec = input.source.toBitVec + input.immediate.toBitVec := by
    rw [addressWord, sourceWord, immediateWord]
    exact (pooled_word_address hp inverse accepted assumptions.initialization.clocks
      assumptions.initialization.image assumptions.wordTable assumptions.subwordTable
      programImage decoded member present family query input.store selected).2.1
  have fetched := run_program_sources programImage entry present
  obtain original | original | original | original | original := pooled_source_cases fetched
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · have localFamily : originalEntry.data.family = .wordMemory := by
      cases mode : originalEntry.data.family
      · simp [ProgramEntry.mapFamily, DecoderData.mapFamily, mode, pooledArithmeticFamily] at family
      · rfl
    rw [mapped_query] at query
    change (⟨.wordMemory, w⟩ : Row p).decoderQuery = originalEntry.query at query
    have selector := row_query_selectors_of_bound limbSize trace.rom.wordMemory
      (row := (⟨.wordMemory, w⟩ : Row p)) (accepted.constraints _ member)
      (by have small := (decoder_field_bounds originalSource.fields).2; omega) query
      ⟨0, by change 0 < 1; decide⟩
    change w 10 = if originalEntry.data.mask.testBit 0 then 1 else 0 at selector
    have fields := originalSource.fields
    change originalEntry.instruction = _ at encoding
    rw [encoding] at fields
    cases mode : input.store
    · cases sourceIndex : input.rs1 with | Regidx rs1 =>
        cases destinationIndex : input.rd with | Regidx rd =>
          simp only [mode, Bool.false_eq_true, if_false, sourceIndex, destinationIndex, decoderFields, instruction] at fields
          split at fields
          · rw [← Option.some.inj fields] at localFamily
            cases localFamily
          · have selected : w 10 = 0 := by simpa [← Option.some.inj fields] using selector
            refine ⟨addressFor (by simpa [mode] using selected), ?_⟩
            simp only [mode, Bool.false_eq_true, if_false]
            have written := word_history_load_write limbSize core selected query trace.memoryEpoch normalized
            rw [← Option.some.inj fields] at written
            change run (SailRV32.Functions.wX_bits (.Regidx rd)
              (Word.mk (w 31).val (w 32).val).toBitVec) input.before = .ok () _ at written
            rw [← dataWord] at written
            have projected := projected_step_of_write rd ⟨output.data, output.pc⟩ written
            rw [retired_state_overwrite] at projected
            exact ⟨_, normal, by simpa only [destinationIndex] using projected⟩
    · cases sourceIndex : input.rs1 with | Regidx rs1 =>
        cases secondIndex : input.rs2 with | Regidx rs2 =>
          simp only [mode, if_true, sourceIndex, secondIndex, decoderFields, instruction] at fields
          have selected : w 10 = 1 := by simpa [← Option.some.inj fields] using selector
          refine ⟨addressFor (by simpa [mode] using selected), ?_⟩
          simp only [mode, if_true]
          have written := pooled_word_native_transport (by omega) inverse accepted
            assumptions.initialization.clocks
            (retired_state_image assumptions.initialization.image (Word.mk (w 0).val (w 1).val).toBitVec)
            member true selected normalized
          simp only [if_true] at written
          have address : output.address = Word.mk (w 25).val (w 26).val := by
            simpa only [mode, if_true] using addressWord
          rw [← address, ← dataWord] at written
          have projected := projected_step_of_cell_write (.ram output.address.toBitVec)
            output.data.toBitVec output.pc written
          rw [retired_state_overwrite] at projected
          exact ⟨_, normal, projected⟩
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

end Airbender.WordMemory.Proofs
