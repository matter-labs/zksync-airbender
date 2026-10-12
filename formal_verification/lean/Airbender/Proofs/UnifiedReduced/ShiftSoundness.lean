import Airbender.Review.UnifiedReduced.Shift
import Airbender.Proofs.UnifiedReduced.Shift
import Airbender.Proofs.UnifiedReduced.RegisterReads
import Airbender.Proofs.Arithmetic.WordBytes
import Airbender.Proofs.Sail.ShiftRetirement

namespace Airbender.UnifiedReduced.Shift.Proofs
open Binary Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private def immediateWord (input : Input) : Word :=
  if input.operation = .rev8 then ⟨0, 0⟩ else if input.immediate then
    ⟨(input.encodedImmediate.extractLsb' 0 6).toNat, 0⟩ else ⟨0, 0⟩

private def metadata (input : Input) : DecoderData UnifiedFamily :=
  ⟨.machine, match input.rs1 with | .Regidx index => index,
    if input.immediate || input.operation = .rev8 then 0 else match input.rs2 with | .Regidx index => index,
    match input.rd with | .Regidx index => index,
    immediateWord input, 32768, input.operation.tag⟩

private theorem decoded_metadata {input : Input} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : instruction input = some entry.instruction) :
    entry.data = metadata input ∧ input.operation.isShift = true ∧
      (input.immediate = true → input.operation ≠ .rev8 → (input.encodedImmediate.extractLsb' 0 6).toNat < 32) := by
  rcases input with ⟨operation, immediate, left, right, pc, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, encoded, before⟩
  change BitVec 5 at rs1 rs2 rd
  cases operation <;> cases immediate <;> simp [instruction] at encoding
  all_goals rw [← encoding] at fields
  all_goals by_cases zero : rd = (0#5)
  all_goals simp [decoderFields, Trace.decoderFields, JumpBranchSlt.decoderFields,
    ShiftBinop.decoderFields, ShiftBinop.instructionFields, binaryFields,
    DecoderData.mapFamily, metadata, immediateWord, ShiftBinop.Operation.tag, ShiftBinop.Operation.isShift,
    zero] at fields ⊢
  all_goals simp_all

private theorem right_low_byte [Fact p.Prime] (hp : 65536 < p)
    (inverse : 256 * (-7864320 : ZMod p) = 1) {w : Nat → ZMod p}
    (small : (w 76).val < 256 ∧ (-7864320 * (w 42 - w 76)).val < 256) :
    (w 76).val = ((rightWord w).toBitVec.extractLsb' 0 8).toNat := by
  have packed := byte_pair_value hp (w 76) (-7864320 * (w 42 - w 76)) (w 42) small.1 small.2
    (by linear_combination (w 42 - w 76) * inverse)
  simp only [rightWord, Word.toBitVec, Word.value, limbBase, BitVec.extractLsb',
    BitVec.toNat_ofNat, Nat.shiftRight_zero]
  norm_num only [Nat.reducePow]
  rw [packed]
  omega

theorem soundness_from_history [Fact p.Prime] (hp : 524288 < p)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {setup : Table (ZMod p) (fields 10)} {initial : State} {cells : List Cell}
    {input : Input} {output : Output} {w : Nat → ZMod p} {after : State} {epoch : Nat}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w importedConstraintsTraceColumns.execute = 1)
    (setupBinding : setup = Setup.table initial)
    (history : SailHistory cells (rowEvents epoch (⟨.machine, w⟩ : Row p UnifiedFamily)).reverse input.before after)
    (rightBound : (readToken w importedConstraintsMemoryPorts[1]).word.Bounded)
    (words : WordMapping input output w)
    {entry : ProgramEntry} (fields : decoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) (encoding : instruction input = some entry.instruction)
    (pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before) :
    ShiftBinop.spec input output := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have decoderSize : 524288 < p := hp
  have arithmeticSize : 131072 < p := by omega
  obtain ⟨dataFields, shift, legal⟩ := decoded_metadata fields encoding
  have flags := UnifiedReduced.Proofs.decoder_selectors decoderSize core
    (UnifiedReduced.Proofs.decoder_field_bounds fields).2.1 query
  have selected : w 26 = 1 ∧ w 27 = 0 := by
    have shift := flags 15
    have operation := flags 16
    rw [dataFields] at shift operation
    constructor
    · simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using shift
    · simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using operation
  have other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 := by
    have ignored (i : Fin 4) : w (21 + i.val) = 0 := by
      have flag := flags ⟨10 + i.val, by have := i.isLt; omega⟩
      rw [dataFields] at flag
      fin_cases i
      all_goals simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
    exact ⟨ignored 0, ignored 1, ignored 2, ignored 3⟩
  have load : w 28 = 0 := by
    have flag := flags 17
    rw [dataFields] at flag
    simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  have immediate : w 8 = (entry.data.immediate.lo : ZMod p) ∧
      w 9 = (entry.data.immediate.hi : ZMod p) := by
    have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
    have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
    change w 8 = (entry.data.immediate.lo : ZMod p) at low
    change w 9 = (entry.data.immediate.hi : ZMod p) at high
    exact ⟨low, high⟩
  have funct3 : w 10 = (input.operation.tag : ZMod p) := by
    have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
    change w 10 = (entry.data.funct3 : ZMod p) at tag
    rw [dataFields] at tag
    exact tag
  have valid : input.operation.tag = 1 ∨ input.operation.tag = 2 ∨ input.operation.tag = 3 ∨ input.operation.tag = 5 := by
    cases operation : input.operation <;> simp_all [ShiftBinop.Operation.isShift, ShiftBinop.Operation.tag]
  have tag : (w 10).val = input.operation.tag := by
    rw [funct3, ZMod.val_natCast, Nat.mod_eq_of_lt]
    rcases valid with e | e | e | e <;> rw [e] <;> omega
  have modelCore := core
  rw [setupBinding] at modelCore
  have registers := UnifiedReduced.Proofs.register_reads limbSize core load query epoch history
  rw [dataFields] at registers immediate
  have leftBytes := UnifiedReduced.Proofs.shift_left_bytes (by dsimp [limbBase] at limbSize; omega)
    byteInverse modelCore selected other
  have truncated := UnifiedReduced.Proofs.shift_amount (by omega) modelCore selected other load
  have lowByte := right_low_byte (by dsimp [limbBase] at limbSize; omega) byteInverse ⟨truncated.1, truncated.2.1⟩
  have unused : input.immediate = true ∨ input.operation = .rev8 → w 42 = 0 := by
    intro unused
    have bounded := rightBound
    have bounded : (rightWord w).Bounded := by
      simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
        importedConstraintsMemoryPorts, rightWord] using bounded
    have zero := registers.2
    have zeroIndex : (metadata input).rs2 = 0 := by
      rcases unused with form | reverse
      · simp [metadata, form]
      · simp [metadata, reverse]
    rw [zeroIndex] at zero
    change EStateM.Result.ok (0 : BitVec 32) input.before = .ok (rightWord w).toBitVec input.before at zero
    have limbs := Word.eq_zero_of_bounded bounded (EStateM.Result.ok.inj zero).1.symm
    apply ZMod.val_injective
    simpa [rightWord] using congrArg Word.lo limbs
  have zeroAmount : input.immediate = true ∨ input.operation = .rev8 → w 57 = 0 := by
    intro unusedPort
    have packed := byte_pair_value (by dsimp [limbBase] at limbSize; omega)
      (w 76) (-7864320 * (w 42 - w 76)) (w 42) truncated.1 truncated.2.1
      (by linear_combination (w 42 - w 76) * byteInverse)
    rw [unused unusedPort, ZMod.val_zero] at packed
    have zero : (w 76).val = 0 := by omega
    apply ZMod.val_injective
    simpa [zero] using truncated.2.2
  have amount : (w 57 + w 8).val = shiftCount input := by
    by_cases reverse : input.operation = .rev8
    · have scratch := zeroAmount (Or.inr reverse)
      have payload : w 8 = 0 := by simpa [metadata, immediateWord, reverse] using immediate.1
      simp [shiftCount, reverse, scratch, payload]
    · cases form : input.immediate
      · have payload : w 8 = 0 := by simpa [metadata, immediateWord, reverse, form] using immediate.1
        rw [payload, add_zero, truncated.2.2, lowByte, Verification.low_byte_shift_amount]
        simp [shiftCount, reverse, form, words.right, rightOperand]
      · have scratch := zeroAmount (Or.inl form)
        have payload : w 8 = ((input.encodedImmediate.extractLsb' 0 6).toNat : ZMod p) := by
          simpa [metadata, immediateWord, reverse, form] using immediate.1
        have bound := legal form reverse
        have same : (input.encodedImmediate.extractLsb' 0 6).toNat = (input.encodedImmediate.extractLsb' 0 5).toNat := by
          simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] at bound ⊢
          norm_num at bound ⊢
          omega
        rw [scratch, zero_add, payload, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), same]
        simp [shiftCount, reverse, form]
  have result := UnifiedReduced.Proofs.shift_destination (by dsimp [limbBase] at limbSize; omega)
    modelCore selected other input.left (words.left.symm ▸ leftBytes)
    (by simpa only [tag] using valid) (by
      intro reverseTag
      have reverse : input.operation = .rev8 := by
        rw [tag] at reverseTag
        cases operation : input.operation <;> simp_all [ShiftBinop.Operation.tag]
      rw [amount]
      simp [shiftCount, reverse])
  change (destination w).toBitVec = _ at result
  rw [← words.result, tag, amount] at result
  have leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.left input.before := by
    rw [words.left]
    cases first : input.rs1 with | Regidx index =>
      simpa [metadata, first, leftWord] using registers.1
  have rightRead : input.immediate = false → input.operation ≠ .rev8 →
      run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right input.before := by
    intro form reverse
    rw [words.right]
    cases second : input.rs2 with | Regidx index =>
      simpa [metadata, second, rightOperand, form, reverse, rightWord] using registers.2
  have canonical := native_query_pc_word limbSize query
  change initialPC w = Word.ofBitVec entry.pc at canonical
  have pcBound : input.pc.Bounded := by
    rw [words.pc, canonical]
    exact Word.ofBitVec_bound _
  have successor := UnifiedReduced.Proofs.pc_successor arithmeticSize core (active) other
    (initial := input.pc) (final := output.pc) (by
      rw [words.pc, words.nextPC]
      exact ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩) pcBound
  exact retire_shift input output shift leftRead rightRead pcRead successor.2.2 result


theorem soundness_from_memory [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : State} {cells : List Cell} {program : List ProgramEntry}
    {projection : SailRV32.instruction → Option (DecoderData UnifiedFamily)}
    (inputs : NativeInputs projection trace initial cells program) (accepted : Accepted trace)
    (memory : MemoryExecution trace initial cells) (setup : trace.rom = Setup.table initial)
    {input : Input} {output : Output} {w : Nat → ZMod p}
    (member : (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows)
    (words : WordMapping input output w)
    (position : RowPosition trace initial cells ⟨.machine, w⟩ input.before)
    {entry : ProgramEntry} (source : entry.SourceWith initial decoderFields)
    (query : decoderQuery w = entry.query)
    (encoding : instruction input = some entry.instruction)
    : ShiftBinop.spec input output := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  obtain ⟨events, after, past, history⟩ := UnifiedReduced.Proofs.row_position_from_memory hp clockInverse
    accepted inputs.clocks memory position
  have bounded := (UnifiedReduced.Proofs.value_bounds hp clockInverse accepted inputs.clocks inputs.image).1
    ⟨.machine, w⟩ member importedConstraintsMemoryPorts[1]
    (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := position
    rw [state, words.pc]
    exact retired_state_pc middle _
  exact soundness_from_history (by dsimp [timestampBase] at hp; omega) byteInverse core
    (accepted.active _ member) setup history bounded words source.fields query encoding pcRead

theorem soundness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) ShiftBinop.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  obtain ⟨addresses, image⟩ := assumptions.initialization.programImage
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  exact soundness_from_memory hp clockInverse byteInverse assumptions.initialization accepted
    (UnifiedReduced.Proofs.memory_execution hp clockInverse accepted assumptions.initialization decoded)
    assumptions.setup member mapping.words mapping.state (run_program_sources image entry present)
    query encoding

end Airbender.UnifiedReduced.Shift.Proofs
