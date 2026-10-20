import Human.Circuits.UnifiedReduced.Model
import Slop.UnifiedReduced.AddSub
import Slop.UnifiedReduced.RegisterReads
import Slop.AddSub.DecodedInterface

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

private theorem arithmetic_metadata {entry : ProgramEntry} {input : Input}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = arithmeticInstruction input) :
    entry.data = arithmeticFields (AddSub.Proofs.arithmeticData input) := by
  rcases input with ⟨⟨opcode, leftWord, rightWord, immediateWord, pcWord⟩,
    ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, encodedImmediate, encodedUpper, before⟩
  change BitVec 5 at rs1 rs2 rd
  rw [encoding] at fields
  cases opcode <;> by_cases zero : rd = (0#5)
  all_goals simpa [arithmeticInstruction, Sail.instruction, decoderFields, Trace.decoderFields, arithmeticFields,
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

theorem arithmetic_soundness_from_history [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {initial after : State}
    {cells : List Cell} {events : List MemoryAccess} {tokens : List (MemoryToken p)}
    {input : Input} {output : Output} {w : Nat → ZMod p} {epoch : Nat}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w importedConstraintsTraceColumns.execute = 1)
    (image : initialImage initial cells = some tokens)
    (past : SailHistory cells events initial input.before)
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse input.before after)
    (registersInitialized : ∀ index,
      input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index → Cell.register index ∈ cells)
    (bounds : (readToken w importedConstraintsMemoryPorts[0]).word.Bounded ∧
      (readToken w importedConstraintsMemoryPorts[1]).word.Bounded)
    (words : WordMapping input output w)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (encoding : entry.instruction = arithmeticInstruction input)
    (pc : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.row.pc.toBitVec input.before) :
    Sail.spec input output := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have decoderSize : 524288 < p := hp
  have calculationSize : 196608 < p := by omega
  have data := arithmetic_metadata (input := input) fields encoding
  have flags := decoder_selectors decoderSize core (decoder_field_bounds fields).2.1 query
  have selectors := arithmetic_selected data flags
  have bounds : (Word.mk (w 36).val (w 37).val).Bounded ∧
      (Word.mk (w 42).val (w 43).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using bounds
  have leftWord : input.row.left = ⟨(w 36).val, (w 37).val⟩ :=
    congrArg₂ Word.mk words.leftLo words.leftHi
  have rightWord : input.row.right = ⟨(w 42).val, (w 43).val⟩ :=
    congrArg₂ Word.mk words.rightLo words.rightHi
  have immediateWord : input.row.immediate = ⟨(w 8).val, (w 9).val⟩ :=
    congrArg₂ Word.mk words.immediateLo words.immediateHi
  have pcWord : input.row.pc = ⟨(w 0).val, (w 1).val⟩ :=
    congrArg₂ Word.mk words.pcLo words.pcHi
  have offset := native_query_immediate_word limbSize (decoder_field_bounds fields).1 query
  have pcValue := native_query_pc_word limbSize query
  have immediate : input.row.immediate = (AddSub.Proofs.arithmeticData input).immediate := by
    rw [immediateWord]
    simpa [arithmeticFields, DecoderData.mapFamily, importedConstraintsDecoderColumns] using offset.trans (congrArg DecoderData.immediate data)
  have registers := register_reads limbSize core selectors.2 query epoch history
  rw [← leftWord, ← rightWord, data] at registers
  change run (SailRV32.Functions.rX_bits (.Regidx (AddSub.Proofs.arithmeticData input).rs1)) input.before =
    .ok input.row.left.toBitVec input.before ∧
    run (SailRV32.Functions.rX_bits (.Regidx (AddSub.Proofs.arithmeticData input).rs2)) input.before =
    .ok input.row.right.toBitVec input.before at registers
  have original (index : BitVec 5)
      (source : input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index) :=
    image_register_after_history image past index (registersInitialized index source)
  have reference := AddSub.Proofs.reference_interface input
    (leftWord.symm ▸ bounds.1) (rightWord.symm ▸ bounds.2) immediate registers.1 registers.2
    (by cases eq : input.rs1 with | Regidx index => simpa [eq] using original index (Or.inl eq))
    (by cases eq : input.rs2 with | Regidx index => simpa [eq] using original index (Or.inr eq)) pc
  have oldMapping : RowWordMapping input output w := by
    constructor
    all_goals first
      | (rw [words.leftLo]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [words.leftHi]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [words.rightLo]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [words.rightHi]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [words.immediateLo]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [words.immediateHi]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [words.pcLo]; exact (ZMod.natCast_zmod_val _).symm)
      | exact words.pcHi
      | exact words.destinationIndex
      | exact words.outputLo
      | exact words.outputHi
      | exact words.finalPCLo
      | exact words.finalPCHi
  have interfaces : RowInterfaces input output w := {
    decoder := ⟨active, selectors.1, reference.1⟩
    ranges := fun _ => ⟨leftWord.symm ▸ bounds.1, rightWord.symm ▸ bounds.2,
      immediateWord.symm ▸ offset.symm ▸ (decoder_field_bounds fields).1⟩
    initialPCLoBound := (pcWord.symm ▸ pcValue.symm ▸ Word.ofBitVec_bound entry.pc).1
    registers := reference.2 }
  exact standard_soundness calculationSize setup input output w ⟨interfaces, core, oldMapping⟩

theorem arithmetic_soundness_from_memory [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (inputs : NativeInputs projection trace initial cells program) (accepted : Accepted trace)
    (memory : MemoryExecution trace initial cells)
    {input : Input} {output : Output} {w : Nat → ZMod p}
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    (registersInitialized : ∀ index,
      input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index → Cell.register index ∈ cells)
    (words : WordMapping input output w)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (encoding : entry.instruction = arithmeticInstruction input) :
    Sail.spec input output := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  obtain ⟨events, after, past, history⟩ := row_position_from_memory hp inverse accepted
    inputs.clocks memory position
  have ranges := (value_bounds hp inverse accepted inputs.clocks inputs.image).1 _ member
  have bounds := And.intro
    (ranges importedConstraintsMemoryPorts[0]
      (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]))
    (ranges importedConstraintsMemoryPorts[1]
      (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]))
  have pcWord : input.row.pc = ⟨(w 0).val, (w 1).val⟩ :=
    congrArg₂ Word.mk words.pcLo words.pcHi
  have pc : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.row.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := position
    rw [state, pcWord]
    exact retired_state_pc middle _
  exact arithmetic_soundness_from_history (by dsimp [timestampBase] at hp; omega)
    core (accepted.active _ member) (retired_state_image inputs.image
      (Word.mk (w 0).val (w 1).val).toBitVec) past history registersInitialized bounds words fields query
    encoding pc

theorem trace_soundness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) Sail.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  obtain ⟨addresses, image⟩ := assumptions.initialization.programImage
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  exact arithmetic_soundness_from_memory hp inverse assumptions.initialization accepted
    (memory_execution hp inverse accepted assumptions.initialization decoded) member
    assumptions.registersInitialized mapping.words mapping.state
    (run_program_sources image entry present).fields query encoding

end Airbender.UnifiedReduced.Proofs
