import Airbender.Proofs.UnifiedReduced.ControlContext
import Airbender.Proofs.JumpBranchSlt.BranchSoundness

namespace Airbender.UnifiedReduced.Control.Branch.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private def metadata (input : Input) : DecoderData UnifiedFamily :=
  ⟨.machine, match input.rs1 with | .Regidx bits => bits,
    match input.rs2 with | .Regidx bits => bits, 0,
    Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) input.encodedOffset),
    24576, JumpBranchSlt.Branch.funct3 input.opcode⟩

private theorem decoded_metadata {input : Input} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = instruction input) : entry.data = metadata input := by
  rw [encoding] at fields
  rcases input with ⟨op, left, right, offset, pc, ⟨rs1⟩, ⟨rs2⟩, imm, before⟩
  simpa [instruction, decoderFields, Trace.decoderFields, JumpBranchSlt.decoderFields,
    jumpFields, DecoderData.mapFamily, metadata] using fields.symm

theorem soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) JumpBranchSlt.Branch.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  change FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints trace.rom) at core
  obtain ⟨addresses, image⟩ := assumptions.initialization.programImage
  obtain ⟨events, after, past, history⟩ := UnifiedReduced.Proofs.row_position clockSize inverse
    accepted assumptions.initialization decoded mapping.state
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  have source := run_program_sources image entry present
  have fields := decoded_metadata source.fields encoding
  obtain ⟨jumps, comparison, branch, mask, binary, noLoad, noStore, noROM⟩ :=
    Control.Proofs.selectors (by omega) core source.fields query true (by rw [fields]; rfl)
  simp only [↓reduceIte] at comparison branch mask
  have total : w 21 + w 22 + w 23 + w 24 = 1 := by simp [jumps.1, jumps.2, comparison, branch]
  have signSource := Control.Proofs.right_sign_source core total
  simp only [comparison, zero_mul, add_zero] at signSource
  have ranges := (UnifiedReduced.Proofs.value_bounds clockSize inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image).1 _ member
  have leftBound : input.left.Bounded := by
    have bound := ranges importedConstraintsMemoryPorts[0]
      (Array.getElem_mem (by change 0 < 3; decide))
    simpa [mapping.words.left, read_word, Row.ports, CircuitLayout.ports,
      importedConstraintsMemoryPorts, WordColumns.evaluate, leftWord] using bound
  have rightBound : input.right.Bounded := by
    have bound := ranges importedConstraintsMemoryPorts[1]
      (Array.getElem_mem (by change 1 < 3; decide))
    simpa [mapping.words.right, read_word, Row.ports, CircuitLayout.ports,
      importedConstraintsMemoryPorts, WordColumns.evaluate, rightWord] using bound
  have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
  change w 10 = (entry.data.funct3 : ZMod p) at tag
  rw [fields] at tag
  have tagBound : (metadata input).funct3 < 8 := by
    cases op : input.opcode <;> simp [metadata, JumpBranchSlt.Branch.funct3, op]
  have smallTag : (w 10).val < 8 := by
    rw [tag, ZMod.val_natCast_of_lt (lt_of_lt_of_le tagBound (by omega))]
    exact tagBound
  have modelCore := core
  rw [assumptions.setup] at modelCore
  have projected := UnifiedReduced.Proofs.control_constraints hp modelCore jumps
    (by rw [comparison, branch]; simp) (by simp [mask]) binary noROM
    (by simpa [mapping.words.left, leftWord, limbBase] using leftBound.2)
    (by simpa [signSource, mapping.words.right, rightWord, limbBase] using rightBound.2) smallTag
  have canonical := native_query_pc_word limbSize query
  change initialPC w = Word.ofBitVec entry.pc at canonical
  have pcBound : input.pc.Bounded := by rw [mapping.words.pc, canonical]; exact Word.ofBitVec_bound _
  have offset : input.offset = (metadata input).immediate := by
    rw [mapping.words.offset]
    exact (native_query_immediate_word limbSize
      (UnifiedReduced.Proofs.decoder_field_bounds source.fields).1 query).trans (congrArg DecoderData.immediate fields)
  have offsetBound : input.offset.Bounded := by rw [offset]; exact Word.ofBitVec_bound _
  have registers := UnifiedReduced.Proofs.register_reads limbSize core noLoad query trace.memoryEpoch history
  rw [fields] at registers
  have leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.left.toBitVec input.before := by
    cases first : input.rs1
    simpa [metadata, first, mapping.words.left, leftWord] using registers.1
  have rightRead : run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right.toBitVec input.before := by
    cases second : input.rs2
    simpa [metadata, second, mapping.words.right, rightWord] using registers.2
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := mapping.state
    rw [state, mapping.words.pc]
    exact retired_state_pc middle _
  have pcAligned : input.pc.lo % 4 = 0 := by
    have aligned := assumptions.codeAligned entry present
    rw [mapping.words.pc, canonical]
    dsimp [Word.ofBitVec, limbBase]
    omega
  have offsetEven : input.offset.lo % 2 = 0 := by
    have parity := Reference.Sail.decoded_offset_even entry.bits initial entry.instruction initial source.decoded
    rw [encoding] at parity
    change input.encodedOffset.toNat % 2 = 0 at parity
    rw [offset]
    exact Reference.Sail.sign_extend_low_even (by decide) _ parity
  have csrs := sail_history_control_flow_csrs past
  simp [retiredState, Std.ExtDHashMap.get?_insert] at csrs
  have misaRead : ∃ value, run (SailRV32.readReg .misa) input.before = .ok value input.before := by
    obtain ⟨value, read⟩ := assumptions.isa
    refine ⟨value, read_register ?_⟩
    simpa [retiredState, Std.ExtDHashMap.get?_insert] using csrs.1.trans read
  have rowMapping : JumpBranchSlt.Branch.RowWordMapping input output (UnifiedReduced.Proofs.controlAssignment w) := by
    refine { operands := ?_, pcOffset := ?_, destination := ?_, rs1Index := ?_, rs2Index := ?_ }
    · rw [mapping.words.left, mapping.words.right]
      exact ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
        (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm⟩
    · rw [mapping.words.pc, mapping.words.offset, mapping.words.nextPC]
      exact ⟨rfl, rfl, (ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩
    · rw [mapping.words.result]; exact ⟨rfl, rfl⟩
    · have index := congrArg (fun q : Vector (ZMod p) 9 => q[2]) query
      change w 5 = (entry.data.rs1.toNat : ZMod p) at index
      rw [fields] at index
      cases first : input.rs1
      simpa [metadata, first, UnifiedReduced.Proofs.controlAssignment, JumpBranchSlt.Variables.rs1Index] using index
    · have index := congrArg (fun q : Vector (ZMod p) 9 => q[3]) query
      change w 6 = (entry.data.rs2.toNat : ZMod p) at index
      rw [fields] at index
      cases second : input.rs2
      simpa [metadata, second, UnifiedReduced.Proofs.controlAssignment, JumpBranchSlt.Variables.rs2Index] using index
  have interface : JumpBranchSlt.Branch.RowInterfaces input output (UnifiedReduced.Proofs.controlAssignment w) := {
    active := accepted.active _ member
    selected := branch
    otherSelectors := ⟨jumps.1, jumps.2, comparison⟩
    conditionTag := tag
    discardedDestination := mask
    leftBound := leftBound
    rightBound := rightBound
    offsetBound := offsetBound
    initialPCLoBound := pcBound.1
    pcAligned := pcAligned
    offsetEven := offsetEven
    finalPCHiBound := by simpa [mapping.words.nextPC, finalPC] using (UnifiedReduced.Proofs.pc_bounds core).2
    signExtension := by rw [offset]; exact Word.ofBitVec_roundtrip _
    leftRead := leftRead
    rightRead := rightRead
    pcRead := pcRead
    misaRead := misaRead }
  exact JumpBranchSlt.Proofs.branch_soundness hp input output _ ⟨interface, projected, rowMapping⟩

end Airbender.UnifiedReduced.Control.Branch.Proofs
