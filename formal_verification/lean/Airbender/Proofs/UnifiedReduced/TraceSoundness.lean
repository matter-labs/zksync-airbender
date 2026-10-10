import Airbender.Review.UnifiedReduced.Model
import Airbender.Proofs.UnifiedReduced.AddSub
import Airbender.Proofs.UnifiedReduced.RegisterReads
import Airbender.Proofs.AddSub.DecodedInterface

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

private theorem arithmetic_metadata {entry : ProgramEntry} {input : Input}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = match input.row.opcode with
      | .add => .RTYPE (input.rs2, input.rs1, input.rd, .ADD)
      | .addi => .ITYPE (input.encodedImmediate, input.rs1, input.rd, .ADDI)
      | .sub => .RTYPE (input.rs2, input.rs1, input.rd, .SUB)
      | .lui => .UTYPE (input.encodedUpperImmediate, input.rd, .LUI)
      | .auipc => .UTYPE (input.encodedUpperImmediate, input.rd, .AUIPC)) :
    entry.data = arithmeticFields (AddSub.Proofs.arithmeticData input) := by
  rcases input with ⟨⟨opcode, leftWord, rightWord, immediateWord, pcWord⟩,
    ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, encodedImmediate, encodedUpper, before⟩
  change BitVec 5 at rs1 rs2 rd
  rw [encoding] at fields
  cases opcode <;> by_cases zero : rd = (0#5)
  all_goals simpa [decoderFields, Trace.decoderFields, arithmeticFields,
    AddSub.Proofs.arithmeticData, Trace.arithmeticFields, DecoderData.mapFamily, zero] using fields.symm

private theorem arithmetic_selected {input : Input} {entry : ProgramEntry}
    {w : Nat → ZMod p}
    (data : entry.data = arithmeticFields (AddSub.Proofs.arithmeticData input))
    (flags : ∀ i : Fin 19, w importedConstraintsDecoderColumns.flags[i] =
      if entry.data.mask.testBit i.val then 1 else 0) :
    w Variables.dispatchColumns[standardSelector input] = 1 ∧ w 28 = 0 := by
  have flag := flags ⟨(standardSelector input).val, by have := (standardSelector input).isLt; omega⟩
  have ram := flags 17
  rw [data] at flag ram
  rcases input with ⟨⟨opcode, leftWord, rightWord, immediateWord, pcWord⟩,
    ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, encodedImmediate, encodedUpper, before⟩
  change BitVec 5 at rs1 rs2 rd
  cases opcode <;> by_cases zero : rd = (0#5)
  all_goals constructor
  all_goals first
    | simpa [standardSelector, zeroRegister, arithmeticFields, AddSub.Proofs.arithmeticData,
        Trace.arithmeticFields, DecoderData.mapFamily, zero, Nat.testBit,
        Nat.shiftRight_eq_div_pow, Variables.dispatchColumns, importedConstraintsDecoderColumns] using flag
    | simpa [arithmeticFields, AddSub.Proofs.arithmeticData, Trace.arithmeticFields,
        DecoderData.mapFamily, zero, Nat.testBit, Nat.shiftRight_eq_div_pow,
        importedConstraintsDecoderColumns] using ram

theorem trace_soundness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  have limbSize : limbBase < p := by dsimp [limbBase, timestampBase] at *; omega
  have decoderSize : 524288 < p := by dsimp [timestampBase] at hp; omega
  have calculationSize : 196608 < p := by dsimp [timestampBase] at hp; omega
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  obtain ⟨addresses, image⟩ := assumptions.initialization.programImage
  obtain ⟨events, after, past, history⟩ := row_position hp inverse accepted
    assumptions.initialization decoded mapping.state
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  have source := run_program_sources image entry present
  have data := arithmetic_metadata source.fields encoding
  have flags := decoder_selectors decoderSize core (decoder_field_bounds source.fields).2.1 query
  have selectors := arithmetic_selected data flags
  have ranges := (value_bounds hp inverse accepted assumptions.initialization.clocks
    assumptions.initialization.image).1 _ member
  have l := ranges importedConstraintsMemoryPorts[0]
    (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have r := ranges importedConstraintsMemoryPorts[1]
    (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have bounds : (Word.mk (w 36).val (w 37).val).Bounded ∧
      (Word.mk (w 42).val (w 43).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using And.intro l r
  have leftWord : input.row.left = ⟨(w 36).val, (w 37).val⟩ :=
    congrArg₂ Word.mk mapping.words.leftLo mapping.words.leftHi
  have rightWord : input.row.right = ⟨(w 42).val, (w 43).val⟩ :=
    congrArg₂ Word.mk mapping.words.rightLo mapping.words.rightHi
  have immediateWord : input.row.immediate = ⟨(w 8).val, (w 9).val⟩ :=
    congrArg₂ Word.mk mapping.words.immediateLo mapping.words.immediateHi
  have pcWord : input.row.pc = ⟨(w 0).val, (w 1).val⟩ :=
    congrArg₂ Word.mk mapping.words.pcLo mapping.words.pcHi
  have offset := native_query_immediate_word limbSize (decoder_field_bounds source.fields).1 query
  have pcValue := native_query_pc_word limbSize query
  have immediate : input.row.immediate = (AddSub.Proofs.arithmeticData input).immediate := by
    rw [immediateWord]
    simpa [arithmeticFields, DecoderData.mapFamily, importedConstraintsDecoderColumns] using offset.trans (congrArg DecoderData.immediate data)
  have registers := register_reads limbSize core selectors.2 query trace.memoryEpoch history
  rw [← leftWord, ← rightWord, data] at registers
  change run (SailRV32.Functions.rX_bits (.Regidx (AddSub.Proofs.arithmeticData input).rs1)) input.before =
    .ok input.row.left.toBitVec input.before ∧
    run (SailRV32.Functions.rX_bits (.Regidx (AddSub.Proofs.arithmeticData input).rs2)) input.before =
    .ok input.row.right.toBitVec input.before at registers
  have original (index : BitVec 5)
      (source : input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index) := image_register_after_history
    (retired_state_image assumptions.initialization.image
      (Word.mk (w 0).val (w 1).val).toBitVec) past index (assumptions.registersInitialized index source)
  have pc : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.row.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := mapping.state
    rw [state, pcWord]
    exact retired_state_pc middle _
  have reference := AddSub.Proofs.reference_interface input
    (leftWord.symm ▸ bounds.1) (rightWord.symm ▸ bounds.2) immediate registers.1 registers.2
    (by cases eq : input.rs1 with | Regidx index => simpa [eq] using original index (Or.inl eq))
    (by cases eq : input.rs2 with | Regidx index => simpa [eq] using original index (Or.inr eq)) pc
  have oldMapping : RowWordMapping input output w := by
    constructor
    all_goals first
      | (rw [mapping.words.leftLo]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [mapping.words.leftHi]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [mapping.words.rightLo]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [mapping.words.rightHi]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [mapping.words.immediateLo]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [mapping.words.immediateHi]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [mapping.words.pcLo]; exact (ZMod.natCast_zmod_val _).symm)
      | exact mapping.words.pcHi
      | exact mapping.words.destinationIndex
      | exact mapping.words.outputLo
      | exact mapping.words.outputHi
      | exact mapping.words.finalPCLo
      | exact mapping.words.finalPCHi
  have interfaces : RowInterfaces input output w := {
    decoder := ⟨accepted.active _ member, selectors.1, reference.1⟩
    ranges := fun _ => ⟨leftWord.symm ▸ bounds.1, rightWord.symm ▸ bounds.2,
      immediateWord.symm ▸ offset.symm ▸ (decoder_field_bounds source.fields).1⟩
    initialPCLoBound := (pcWord.symm ▸ pcValue.symm ▸ Word.ofBitVec_bound entry.pc).1
    registers := reference.2 }
  exact standard_soundness calculationSize trace.rom input output w ⟨interfaces, core, oldMapping⟩

end Airbender.UnifiedReduced.Proofs
