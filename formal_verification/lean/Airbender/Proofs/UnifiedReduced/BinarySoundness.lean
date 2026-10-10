import Airbender.Review.UnifiedReduced.Binary
import Airbender.Proofs.UnifiedReduced.BinaryResult
import Airbender.Proofs.UnifiedReduced.RegisterReads
import Airbender.Proofs.Arithmetic.WordBytes
import Airbender.Proofs.Sail.Binop

namespace Airbender.UnifiedReduced.Binary.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private def metadata (input : Input) : DecoderData UnifiedFamily :=
  ⟨.machine, match input.rs1 with | .Regidx index => index,
    match input.rs2 with | .Regidx index => index,
    match input.rd with | .Regidx index => index,
    ⟨0, 0⟩, 65536, Setup.binaryTag input.operation.tag⟩

private theorem decoded_metadata {input : Input} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : instruction input = some entry.instruction) :
    entry.data = metadata input ∧ input.operation.isShift = false ∧ input.immediate = false := by
  rcases input with ⟨operation, immediate, left, right, pc, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, encoded, before⟩
  change BitVec 5 at rs1 rs2 rd
  cases operation <;> cases immediate <;> simp [instruction] at encoding
  all_goals rw [← encoding] at fields
  all_goals by_cases zero : rd = (0#5)
  all_goals simp [decoderFields, Trace.decoderFields, JumpBranchSlt.decoderFields,
    ShiftBinop.decoderFields, ShiftBinop.instructionFields, binaryFields,
    DecoderData.mapFamily, metadata, ShiftBinop.Operation.tag, ShiftBinop.Operation.isShift,
    zero, Setup.binaryTag] at fields ⊢
  all_goals exact fields.symm

private theorem zero_sign [Fact p.Prime] (hp : 256 < p)
    {initial : State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (load : w 28 = 0) (immediate : w 9 = 0) : w 57 = 0 := by
  have gate := Verification.assertion_of_holds holds ⟨42, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment, load] at gate
  have t := Verification.assertion_of_holds holds ⟨48, by rw [constraint_count]; decide⟩
  have a := Verification.assertion_of_holds holds ⟨49, by rw [constraint_count]; decide⟩
  have b := Verification.assertion_of_holds holds ⟨50, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval, Verification.environment,
    selected.1, selected.2, other.1, other.2.1, other.2.2.1, other.2.2.2,
    gate, immediate] at t a b
  have tag : w 88 = 3 := by linear_combination t
  have key : w 89 = 0 := by linear_combination a
  have value : w 90 = w 57 := by linear_combination b
  have query := Verification.lookup_of_holds holds ⟨13, by rw [lookup_count]; decide⟩
  have standard := Setup.Proofs.ordinary_lookup (by omega : 55 ≤ p) query 3 (Or.inl rfl)
    (by simpa [Expression.eval, Verification.environment] using tag)
  have sign := Verification.binary_sign_lookup hp standard
    (by simpa [Expression.eval, Verification.environment] using tag)
  have canonical : (w 57).val = 0 := by
    simpa [Expression.eval, Verification.environment, key, value] using sign.2
  have cast := congrArg (fun n : Nat => (n : ZMod p)) canonical
  simpa only [ZMod.natCast_zmod_val, Nat.cast_zero] using cast

private theorem register_bytes [Fact p.Prime] (hp : 65536 < p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {initial : State} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints (Setup.table initial)))
    (selected : w 26 = 0 ∧ w 27 = 1) (other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (load : w 28 = 0) (immediate : w 8 = 0 ∧ w 9 = 0)
    (tag : Nat) (valid : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (Setup.binaryTag tag : ZMod p)) :
    (∀ i : Fin 4, UnifiedReduced.Proofs.leftByte w i =
      (((leftWord w).toBitVec.extractLsb' (8 * i.val) 8).toNat : ZMod p)) ∧
    (∀ i : Fin 4, UnifiedReduced.Proofs.rightByte w i + UnifiedReduced.Proofs.immediateByte w i =
      (((rightWord w).toBitVec.extractLsb' (8 * i.val) 8).toNat : ZMod p)) := by
  have sign := zero_sign (by omega : 256 < p) holds selected other load immediate.2
  have zero (i : Fin 4) : UnifiedReduced.Proofs.immediateByte w i = 0 := by
    fin_cases i <;> simp [UnifiedReduced.Proofs.immediateByte, immediate.1, immediate.2, sign]
  have values := UnifiedReduced.Proofs.binary_query_values (by omega : 256 < p) holds selected other tag valid funct3
  have leftBound (i : Fin 4) := (values i).1
  have rightBound (i : Fin 4) : (UnifiedReduced.Proofs.rightByte w i).val < 256 := by
    simpa only [zero, add_zero] using (values i).2.1
  have left := Word.byte_fields hp (w 36) (w 37) (UnifiedReduced.Proofs.leftByte w) leftBound
    (by change w 74 + 256 * (-7864320 * (w 36 - w 74)) = w 36
        linear_combination (w 36 - w 74) * inverse)
    (by change w 75 + 256 * (-7864320 * (w 37 - w 75)) = w 37
        linear_combination (w 37 - w 75) * inverse)
  have right := Word.byte_fields hp (w 42) (w 43) (UnifiedReduced.Proofs.rightByte w) rightBound
    (by change w 76 + 256 * (-7864320 * (w 42 - w 76)) = w 42
        linear_combination (w 42 - w 76) * inverse)
    (by change w 77 + 256 * (-7864320 * (w 43 - w 77)) = w 43
        linear_combination (w 43 - w 77) * inverse)
  exact ⟨by simpa only [leftWord] using left,
    fun i => by simpa only [zero, add_zero, rightWord] using right i⟩

theorem soundness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) ShiftBinop.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  have limbSize : limbBase < p := by dsimp [limbBase, timestampBase] at *; omega
  have decoderSize : 524288 < p := by dsimp [timestampBase] at hp; omega
  have arithmeticSize : 131072 < p := by dsimp [timestampBase] at hp; omega
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  obtain ⟨addresses, image⟩ := assumptions.initialization.programImage
  obtain ⟨events, after, past, history⟩ := UnifiedReduced.Proofs.row_position hp clockInverse accepted
    assumptions.initialization decoded mapping.state
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  have source := run_program_sources image entry present
  obtain ⟨dataFields, binary, register⟩ := decoded_metadata source.fields encoding
  have flags := UnifiedReduced.Proofs.decoder_selectors decoderSize core
    (UnifiedReduced.Proofs.decoder_field_bounds source.fields).2.1 query
  have selected : w 26 = 0 ∧ w 27 = 1 := by
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
  have immediate : w 8 = 0 ∧ w 9 = 0 := by
    have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
    have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
    change w 8 = (entry.data.immediate.lo : ZMod p) at low
    change w 9 = (entry.data.immediate.hi : ZMod p) at high
    rw [dataFields] at low high
    simpa [metadata] using And.intro low high
  have funct3 : w 10 = (Setup.binaryTag input.operation.tag : ZMod p) := by
    have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
    change w 10 = (entry.data.funct3 : ZMod p) at tag
    rw [dataFields] at tag
    exact tag
  have valid : input.operation.tag = 4 ∨ input.operation.tag = 6 ∨ input.operation.tag = 7 := by
    cases operation : input.operation <;> simp_all [ShiftBinop.Operation.isShift, ShiftBinop.Operation.tag]
  have modelCore := core
  rw [assumptions.setup] at modelCore
  have bytes := register_bytes (by dsimp [limbBase] at limbSize; omega) byteInverse
    modelCore selected other load immediate input.operation.tag valid funct3
  have result := UnifiedReduced.Proofs.binary_destination (by dsimp [limbBase] at limbSize; omega)
    modelCore selected other input.operation.tag valid funct3
    (mapping.words.left.symm ▸ bytes.1) (mapping.words.right.symm ▸ bytes.2)
  change (destination w).toBitVec = Verification.byteOperation input.operation.tag input.left input.right at result
  rw [← mapping.words.result] at result
  have registers := UnifiedReduced.Proofs.register_reads limbSize core load query trace.memoryEpoch history
  rw [dataFields] at registers
  have leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.left input.before := by
    rw [mapping.words.left]
    cases first : input.rs1 with | Regidx index =>
      simpa [metadata, first, leftWord] using registers.1
  have rightRead : run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right input.before := by
    rw [mapping.words.right]
    cases second : input.rs2 with | Regidx index =>
      simpa [metadata, second, rightWord] using registers.2
  have canonical := native_query_pc_word limbSize query
  change initialPC w = Word.ofBitVec entry.pc at canonical
  have pcBound : input.pc.Bounded := by
    rw [mapping.words.pc, canonical]
    exact Word.ofBitVec_bound _
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := mapping.state
    rw [state, mapping.words.pc]
    exact retired_state_pc middle _
  have successor := UnifiedReduced.Proofs.pc_successor arithmeticSize core (accepted.active _ member) other
    (initial := input.pc) (final := output.pc) (by
      rw [mapping.words.pc, mapping.words.nextPC]
      exact ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩) pcBound
  exact retire_binary_register input output binary register leftRead rightRead pcRead successor.2.2 result

end Airbender.UnifiedReduced.Binary.Proofs
