import Human.Circuits.UnifiedReduced.Binary
import Slop.UnifiedReduced.BinaryOperands
import Slop.UnifiedReduced.BinaryResult
import Slop.UnifiedReduced.RegisterReads
import Slop.Arithmetic.WordBytes
import Slop.Sail.Binop

namespace Airbender.UnifiedReduced.Binary.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

private def metadata (input : Input) : DecoderData UnifiedFamily :=
  ⟨.machine, match input.rs1 with | .Regidx index => index,
    if input.immediate then 0 else match input.rs2 with | .Regidx index => index,
    match input.rd with | .Regidx index => index,
    if input.immediate then ShiftBinop.binaryImmediate
      (SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate) else ⟨0, 0⟩,
    65536, Setup.binaryTag input.operation.tag⟩

private theorem decoded_metadata {input : Input} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : instruction input = some entry.instruction) :
    entry.data = metadata input ∧ input.operation.isShift = false := by
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
  obtain ⟨dataFields, binary⟩ := decoded_metadata fields encoding
  have flags := UnifiedReduced.Proofs.decoder_selectors decoderSize core
    (UnifiedReduced.Proofs.decoder_field_bounds fields).2.1 query
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
  have immediate : w 8 = (entry.data.immediate.lo : ZMod p) ∧
      w 9 = (entry.data.immediate.hi : ZMod p) := by
    have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
    have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
    change w 8 = (entry.data.immediate.lo : ZMod p) at low
    change w 9 = (entry.data.immediate.hi : ZMod p) at high
    exact ⟨low, high⟩
  have funct3 : w 10 = (Setup.binaryTag input.operation.tag : ZMod p) := by
    have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
    change w 10 = (entry.data.funct3 : ZMod p) at tag
    rw [dataFields] at tag
    exact tag
  have valid : input.operation.tag = 4 ∨ input.operation.tag = 6 ∨ input.operation.tag = 7 := by
    cases operation : input.operation <;> simp_all [ShiftBinop.Operation.isShift, ShiftBinop.Operation.tag]
  have modelCore := core
  rw [setupBinding] at modelCore
  have registers := UnifiedReduced.Proofs.register_reads limbSize core load query epoch history
  rw [dataFields] at registers immediate
  have leftBytes := UnifiedReduced.Proofs.binary_left_bytes (by dsimp [limbBase] at limbSize; omega)
    byteInverse modelCore selected other input.operation.tag valid funct3
  have rightBytes : ∀ i : Fin 4, UnifiedReduced.Proofs.rightByte w i + UnifiedReduced.Proofs.immediateByte w i =
      ((input.right.extractLsb' (8 * i.val) 8).toNat : ZMod p) := by
    cases form : input.immediate
    · have plain : w 8 = 0 ∧ w 9 = 0 := by simpa [metadata, form] using immediate
      have right := UnifiedReduced.Proofs.binary_register_bytes (by dsimp [limbBase] at limbSize; omega)
        byteInverse modelCore selected other load plain input.operation.tag valid funct3
      simpa only [words.right, rightOperand, form, Bool.false_eq_true, ite_false, rightWord] using right
    · have bounded := rightBound
      have bounded : (rightWord w).Bounded := by
        simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
          importedConstraintsMemoryPorts, rightWord] using bounded
      have zero := registers.2
      simp only [metadata, form, ite_true] at zero
      change EStateM.Result.ok (0 : BitVec 32) input.before = .ok (rightWord w).toBitVec input.before at zero
      have limbs := Word.eq_zero_of_bounded bounded (EStateM.Result.ok.inj zero).1.symm
      have lo := congrArg Word.lo limbs
      have hi := congrArg Word.hi limbs
      have fields : w 42 = 0 ∧ w 43 = 0 := by
        constructor <;> apply ZMod.val_injective
        · simpa [rightWord] using lo
        · simpa [rightWord] using hi
      have packed : w 8 = ((SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate).extractLsb' 0 8).toNat ∧
          w 9 = ((SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate).extractLsb' 8 8).toNat := by
        simpa [metadata, form, ShiftBinop.binaryImmediate, BitVec.extractLsb'_toNat,
          Nat.shiftRight_eq_div_pow] using immediate
      have right := UnifiedReduced.Proofs.binary_immediate_bytes (by dsimp [limbBase] at limbSize; omega)
        byteInverse modelCore selected other load input.encodedImmediate packed fields input.operation.tag valid funct3
      simpa only [words.right, rightOperand, form, ite_true] using right
  have result := UnifiedReduced.Proofs.binary_destination (by dsimp [limbBase] at limbSize; omega)
    modelCore selected other input.operation.tag valid funct3
    (words.left.symm ▸ leftBytes) rightBytes
  change (destination w).toBitVec = Verification.byteOperation input.operation.tag input.left input.right at result
  rw [← words.result] at result
  have leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.left input.before := by
    rw [words.left]
    cases first : input.rs1 with | Regidx index =>
      simpa [metadata, first, leftWord] using registers.1
  have rightRead : input.immediate = false →
      run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right input.before := by
    intro form
    rw [words.right]
    cases second : input.rs2 with | Regidx index =>
      simpa [metadata, second, rightOperand, form, rightWord] using registers.2
  have immediateValue : input.immediate = true →
      input.right = SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate := by
    intro form
    simpa [rightOperand, form] using words.right
  have canonical := native_query_pc_word limbSize query
  change initialPC w = Word.ofBitVec entry.pc at canonical
  have pcBound : input.pc.Bounded := by
    rw [words.pc, canonical]
    exact Word.ofBitVec_bound _
  have successor := UnifiedReduced.Proofs.pc_successor arithmeticSize core (active) other
    (initial := input.pc) (final := output.pc) (by
      rw [words.pc, words.nextPC]
      exact ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩) pcBound
  exact retire_binary input output binary leftRead rightRead immediateValue pcRead successor.2.2 result


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

end Airbender.UnifiedReduced.Binary.Proofs
