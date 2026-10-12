import Airbender.Review.AddSub.Model
import Airbender.Proofs.Trace.RowContext
import Airbender.Proofs.Trace.Arithmetic

namespace Airbender.AddSub.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Reuse the row calculation after deriving all of its interfaces from the
    shared initialized history and actual Sail decoder. -/
theorem trace_soundness {p : Nat} [Fact p.Prime]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    InterfaceAssumptions trace initial cells program →
    Properties.Soundness (circuitModel trace initial cells program).relation Sail.spec := by
  rintro assumptions input output w ⟨⟨accepted, decoded, member⟩, mapping⟩
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints) importedConstraintsTimestampLookups)
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  obtain ⟨events, after, past, history⟩ := pooled_row_position clockSize inverse
    accepted assumptions.initialization.clocks assumptions.initialization.image
    assumptions.initialization.distinct assumptions.initialization.aligned
    programImage decoded mapping.state
  have readBounds := (pooled_value_bounds (by omega) inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image
    assumptions.wordTable assumptions.subwordTable programImage decoded).1 _ member
  have left := readBounds importedConstraintsMemoryPorts[0]
    (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have right := readBounds importedConstraintsMemoryPorts[1]
    (by change importedConstraintsMemoryPorts[1] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have bounds : (Word.mk (w 25).val (w 26).val).Bounded ∧
      (Word.mk (w 29).val (w 30).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using And.intro left right
  obtain ⟨newer, older, middle, permutation, ordered, writes, atState⟩ := mapping.state
  have pc : run (SailRV32.Functions.get_arch_pc ()) input.before =
      .ok (Word.mk (w 0).val (w 1).val).toBitVec input.before := by
    rw [atState]
    exact retired_state_pc middle _
  obtain ⟨entry, present, family, query, encoding⟩ := mapping.instruction
  have source := run_program_sources programImage entry present
  obtain original | original | original | original | original := pooled_source_cases source
  all_goals obtain ⟨originalEntry, originalSource, equal⟩ := original
  all_goals subst entry
  · rw [mapped_query] at query
    change (⟨.addSub, w⟩ : Row p).decoderQuery = originalEntry.query at query
    change originalEntry.instruction = _ at encoding
    obtain ⟨row, rs1, rs2, rd, immediate, upper, before⟩ := input
    cases rs1 with | Regidx rs1 =>
      cases rs2 with | Regidx rs2 =>
        cases rd with | Regidx rd =>
          have canonical : (⟨row, .Regidx rs1, .Regidx rs2, .Regidx rd, immediate, upper, before⟩ : Input) =
              arithmeticInput row.opcode rs1 rs2 rd immediate upper w before := by
            congr 1
            change RowInput.mk row.opcode row.left row.right row.immediate row.pc = _
            congr 1
            · exact congrArg₂ Word.mk mapping.words.leftLo mapping.words.leftHi
            · exact congrArg₂ Word.mk mapping.words.rightLo mapping.words.rightHi
            · exact congrArg₂ Word.mk mapping.words.immediateLo mapping.words.immediateHi
            · exact congrArg₂ Word.mk mapping.words.pcLo mapping.words.pcHi
          have canonicalOutput : output =
              ⟨⟨(w 33).val, (w 34).val⟩, ⟨(w 19).val, (w 20).val⟩⟩ :=
            congrArg₂ Output.mk (congrArg₂ Word.mk mapping.words.outputLo mapping.words.outputHi)
              (congrArg₂ Word.mk mapping.words.finalPCLo mapping.words.finalPCHi)
          have interface := local_arithmetic_interface (by dsimp [ROM.limit]; omega)
            (retired_state_image assumptions.initialization.image
              (Word.mk (w 0).val (w 1).val).toBitVec)
            trace.rom.wordMemory trace.memoryEpoch (accepted.constraints _ member) (accepted.active _ member)
            ⟨bounds.1, bounds.2, query_immediate limbSize originalSource.fields query⟩
            originalSource.fields query row.opcode rs1 rs2 rd immediate upper
            ⟨assumptions.registersInitialized rs1, assumptions.registersInitialized rs2⟩ encoding past history pc
          have oldMapping : RowWordMapping (arithmeticInput row.opcode rs1 rs2 rd immediate upper w before)
              ⟨⟨(w 33).val, (w 34).val⟩, ⟨(w 19).val, (w 20).val⟩⟩ w := by
            constructor
            all_goals first
              | exact (ZMod.natCast_zmod_val _).symm
              | exact mapping.words.destinationIndex
              | rfl
          have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
            calc
              (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
              _ = 1 := inverse
          rw [canonical, canonicalOutput]
          exact soundness (by omega) arithmeticInverse _ _ w ⟨interface, core, oldMapping⟩
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [ProgramEntry.mapFamily, DecoderData.mapFamily] at family

end Airbender.AddSub.Proofs
