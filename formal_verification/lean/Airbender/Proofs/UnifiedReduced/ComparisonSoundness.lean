import Airbender.Proofs.UnifiedReduced.ControlContext
import Airbender.Proofs.JumpBranchSlt.Soundness

namespace Airbender.UnifiedReduced.Control.Comparison.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384
set_option maxHeartbeats 2800000

private def immediate (op : JumpBranchSlt.Comparison.Opcode) : Bool :=
  match op with | .slti | .sltiu => true | _ => false
private def canonicalInput (input : Input) : Input :=
  { input with rs2 := if immediate input.opcode then zeroRegister else input.rs2 }
private def metadata (input : Input) : DecoderData UnifiedFamily :=
  ⟨.machine, match input.rs1 with | .Regidx bits => bits,
    if immediate input.opcode then 0 else match input.rs2 with | .Regidx bits => bits,
    match input.rd with | .Regidx bits => bits,
    if immediate input.opcode then Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate)
    else ⟨0, 0⟩, 4096, match input.opcode with | .slt | .slti => 2 | _ => 3⟩

private theorem decoded_metadata {input : Input} {entry : ProgramEntry}
    (fields : decoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = instruction input) :
    entry.data = metadata input ∧ input.rd ≠ zeroRegister := by
  rw [encoding] at fields
  rcases input with ⟨op, left, right, pc, ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, imm, before⟩
  change BitVec 5 at rs1 rs2 rd
  cases op <;> by_cases zero : rd = (0#5)
  all_goals simp [instruction, decoderFields, Trace.decoderFields, JumpBranchSlt.decoderFields,
    ShiftBinop.decoderFields, jumpFields, DecoderData.mapFamily, metadata, immediate, zero,
    zeroRegister] at fields ⊢
  all_goals exact fields.symm

theorem soundness [Fact p.Prime] (hp : 4194304 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) JumpBranchSlt.Comparison.spec := by
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
  obtain ⟨fields, nonzero⟩ := decoded_metadata source.fields encoding
  obtain ⟨jumps, comparison, branch, mask, binary, noLoad, noStore, noROM⟩ :=
    Control.Proofs.selectors (by omega) core source.fields query false (by rw [fields]; rfl)
  have total : w 21 + w 22 + w 23 + w 24 = 1 := by simp [jumps.1, jumps.2, comparison, branch]
  have signSource := Control.Proofs.right_sign_source core total
  simp only [comparison, one_mul] at signSource
  have ranges := (UnifiedReduced.Proofs.value_bounds clockSize inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image).1 _ member
  have leftBound : input.left.Bounded := by
    have bound := ranges importedConstraintsMemoryPorts[0] (Array.getElem_mem (by change 0 < 3; decide))
    simpa [mapping.words.left, read_word, Row.ports, CircuitLayout.ports,
      importedConstraintsMemoryPorts, WordColumns.evaluate, leftWord] using bound
  have rightRegisterBound : (rightWord w).Bounded := by
    have bound := ranges importedConstraintsMemoryPorts[1] (Array.getElem_mem (by change 1 < 3; decide))
    simpa [read_word, Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts,
      WordColumns.evaluate, rightWord] using bound
  have registers := UnifiedReduced.Proofs.register_reads limbSize core noLoad query trace.memoryEpoch history
  rw [fields] at registers
  have encoded : w 8 = ((metadata input).immediate.lo : ZMod p) ∧
      w 9 = ((metadata input).immediate.hi : ZMod p) := by
    have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
    have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
    change w 8 = (entry.data.immediate.lo : ZMod p) at low
    change w 9 = (entry.data.immediate.hi : ZMod p) at high
    rw [fields] at low high
    exact ⟨low, high⟩
  have preprocessing : if immediate input.opcode then w 42 = 0 ∧ w 43 = 0 else w 8 = 0 ∧ w 9 = 0 := by
    cases form : immediate input.opcode
    · simpa [metadata, form] using encoded
    · have zero := registers.2
      simp only [metadata, form, if_true] at zero
      change EStateM.Result.ok (0 : BitVec 32) input.before = .ok (rightWord w).toBitVec input.before at zero
      have limbs := Word.eq_zero_of_bounded rightRegisterBound (EStateM.Result.ok.inj zero).1.symm
      constructor <;> apply ZMod.val_injective
      · simpa [rightWord] using congrArg Word.lo limbs
      · simpa [rightWord] using congrArg Word.hi limbs
  have rightValue : input.right = if immediate input.opcode then (metadata input).immediate else rightWord w := by
    rw [mapping.words.right]
    cases form : immediate input.opcode
    · have plain : w 8 = 0 ∧ w 9 = 0 := by simpa [form] using preprocessing
      simp [form, comparisonRight, rightWord, plain.1, plain.2]
    · have zero : w 42 = 0 ∧ w 43 = 0 := by simpa [form] using preprocessing
      simp only [form, if_true, comparisonRight, zero.1, zero.2, zero_add, encoded.1, encoded.2]
      have bounded : (metadata input).immediate.Bounded := by
        simpa [metadata, form] using Word.ofBitVec_bound (SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate)
      exact congrArg₂ Word.mk (ZMod.val_natCast_of_lt (lt_trans bounded.1 limbSize))
        (ZMod.val_natCast_of_lt (lt_trans bounded.2 limbSize))
  have rightBound : input.right.Bounded := by
    rw [rightValue]
    cases form : immediate input.opcode
    · exact rightRegisterBound
    · simpa [metadata, form] using Word.ofBitVec_bound (SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate)
  have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
  change w 10 = (entry.data.funct3 : ZMod p) at tag
  rw [fields] at tag
  have tagBound : (metadata input).funct3 < 8 := by cases op : input.opcode <;> simp [metadata, op]
  have smallTag : (w 10).val < 8 := by rw [tag, ZMod.val_natCast_of_lt (lt_trans tagBound (by omega))]; exact tagBound
  have modelCore := core
  rw [assumptions.setup] at modelCore
  have projected := UnifiedReduced.Proofs.control_constraints hp modelCore jumps
    (by rw [comparison, branch]; simp) (by simp [branch]) binary noROM
    (by simpa [mapping.words.left, leftWord, limbBase] using leftBound.2)
    (by simpa [signSource, mapping.words.right, comparisonRight, limbBase] using rightBound.2) smallTag
  have canonical := native_query_pc_word limbSize query
  change initialPC w = Word.ofBitVec entry.pc at canonical
  have pcBound : input.pc.Bounded := by rw [mapping.words.pc, canonical]; exact Word.ofBitVec_bound _
  have pcAligned : input.pc.lo % 4 = 0 := by
    have aligned := assumptions.codeAligned entry present
    rw [mapping.words.pc, canonical]
    dsimp [Word.ofBitVec, limbBase]
    omega
  have leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.left.toBitVec input.before := by
    cases first : input.rs1
    simpa [metadata, first, mapping.words.left, leftWord] using registers.1
  have rightRead : input.opcode = .slt ∨ input.opcode = .sltu →
      run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right.toBitVec input.before := by
    intro form
    have reg : immediate input.opcode = false := by rcases form with form | form <;> simp [form, immediate]
    rw [rightValue]
    cases second : input.rs2
    simpa [metadata, second, reg, rightWord] using registers.2
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := mapping.state
    rw [state, mapping.words.pc]
    exact retired_state_pc middle _
  have rowMapping : JumpBranchSlt.Comparison.RowWordMapping (canonicalInput input) output (UnifiedReduced.Proofs.controlAssignment w) := by
    refine { leftLo := ?_, leftHi := ?_, rightLo := ?_, rightHi := ?_, rs1Index := ?_, rs2Index := ?_, rdIndex := ?_, pcLo := ?_, pcHi := ?_, outputLo := ?_, outputHi := ?_, finalPCLo := ?_, finalPCHi := ?_ }
    all_goals try dsimp only [canonicalInput]
    all_goals first
      | (rw [mapping.words.left]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [mapping.words.right]; exact (ZMod.natCast_zmod_val _).symm)
      | (rw [mapping.words.pc]; rfl)
      | (rw [mapping.words.result]; rfl)
      | (rw [mapping.words.nextPC]; rfl)
      | (have index := congrArg (fun q : Vector (ZMod p) 9 => q[2]) query
         change w 5 = (entry.data.rs1.toNat : ZMod p) at index
         rw [fields] at index
         cases first : input.rs1
         simpa [metadata, first, UnifiedReduced.Proofs.controlAssignment, JumpBranchSlt.Variables.rs1Index] using index)
      | (have index := congrArg (fun q : Vector (ZMod p) 9 => q[3]) query
         change w 6 = (entry.data.rs2.toNat : ZMod p) at index
         rw [fields] at index
         cases second : input.rs2
         cases form : immediate input.opcode
         all_goals simpa [metadata, canonicalInput, second, form, UnifiedReduced.Proofs.controlAssignment,
           JumpBranchSlt.Variables.rs2Index] using index)
      | (have index := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
         change w 7 = (entry.data.rd.toNat : ZMod p) at index
         rw [fields] at index
         cases rd : input.rd
         simpa [metadata, rd, UnifiedReduced.Proofs.controlAssignment, JumpBranchSlt.Variables.rdIndex] using index)
  have interface : JumpBranchSlt.Comparison.RowInterfaces (canonicalInput input) output (UnifiedReduced.Proofs.controlAssignment w) := {
    active := accepted.active _ member
    selected := comparison
    otherSelectors := ⟨jumps.1, jumps.2, branch⟩
    preprocessing := by
      cases op : input.opcode
      all_goals simp [op, immediate] at preprocessing
      all_goals simpa [canonicalInput, op, immediate, UnifiedReduced.Proofs.controlAssignment,
        JumpBranchSlt.Variables.rs2Lo, JumpBranchSlt.Variables.rs2Hi,
        JumpBranchSlt.Variables.immediateLo, JumpBranchSlt.Variables.immediateHi] using preprocessing
    funct3 := by cases op : input.opcode <;> simpa [metadata, canonicalInput, op, UnifiedReduced.Proofs.controlAssignment, JumpBranchSlt.Variables.conditionTag] using tag
    nonzeroSelector := mask
    nonzeroDestination := nonzero
    leftBound := leftBound
    rightBound := rightBound
    initialPCLoBound := pcBound.1
    pcAligned := pcAligned
    finalPCHiBound := by simpa [mapping.words.nextPC, finalPC] using (UnifiedReduced.Proofs.pc_bounds core).2
    leftRead := leftRead
    rightRead := by
      intro form
      have form : input.opcode = .slt ∨ input.opcode = .sltu := form
      have reg : immediate input.opcode = false := by rcases form with form | form <;> simp [form, immediate]
      simpa [canonicalInput, reg] using rightRead form
    signExtension := by
      intro form
      have form : input.opcode = .slti ∨ input.opcode = .sltiu := form
      have imm : immediate input.opcode = true := by rcases form with form | form <;> simp [form, immediate]
      change input.right.toBitVec = SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate
      rw [rightValue]
      simpa [imm, metadata] using Word.ofBitVec_roundtrip (SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate)
    pcRead := pcRead }
  have result := JumpBranchSlt.Proofs.comparison_soundness hp (canonicalInput input) output _ ⟨interface, projected, rowMapping⟩
  cases op : input.opcode
  all_goals simpa [JumpBranchSlt.Comparison.spec, JumpBranchSlt.Comparison.execution,
    canonicalInput, immediate, op] using result

end Airbender.UnifiedReduced.Control.Comparison.Proofs
