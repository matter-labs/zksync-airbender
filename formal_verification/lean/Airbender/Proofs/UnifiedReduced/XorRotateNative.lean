import Airbender.Review.UnifiedReduced.XorRotate
import Airbender.Proofs.UnifiedReduced.XorRotateArithmetic
import Airbender.Proofs.UnifiedReduced.TriAddNative

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem xorrot_metadata {entry : ProgramEntry} {input : XorRotate.Input}
    (fields : customDecoderFields entry.instruction = some entry.data)
    (encoding : entry.instruction = XorRotate.instruction input) :
    entry.data = ⟨.machine, (match input.rs1 with | .Regidx bits => bits),
      (match input.rd with | .Regidx bits => bits), (match input.rd with | .Regidx bits => bits),
      ⟨0, 0⟩, 65536, 47 + input.rotation.val⟩ ∧ input.rd ≠ zeroRegister := by
  rcases input with ⟨rotation, left, old, ⟨rs1⟩, ⟨rd⟩, pc, before⟩
  rw [encoding] at fields
  by_cases zero : rd = 0
  · fin_cases rotation <;> simp [XorRotate.instruction, XorRotate.amount, customDecoderFields, zero] at fields
  · constructor
    · have result : rd ≠ (0 : BitVec 5) ∧ entry.data =
          ⟨.machine, rs1, rd, rd, ⟨0, 0⟩, 65536, 47 + rotation.val⟩ := by
        fin_cases rotation
        all_goals simpa [XorRotate.instruction, XorRotate.amount, customDecoderFields, customRotationTag] using fields.symm
      exact result.2
    · simpa [zeroRegister] using zero

theorem native_xorrot_soundness [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    (trace : UnifiedTrace p) (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    (XorRotate.circuitModel trace initial cells program).SoundnessUnder
      (XorRotate.InterfaceAssumptions trace initial cells program) XorRotate.spec := by
  rintro input output w ⟨assumptions, ⟨accepted, decoded, member⟩, mapping⟩
  have limbSize : limbBase < p := by dsimp [limbBase, timestampBase] at *; omega
  have decoderSize : 524288 < p := by dsimp [timestampBase] at hp; omega
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
  obtain ⟨addresses, image⟩ := assumptions.initialization.programImage
  obtain ⟨events, after, past, history⟩ := custom_row_position hp clockInverse accepted
    assumptions.initialization decoded mapping.state
  obtain ⟨entry, present, query, encoding⟩ := mapping.instruction
  have source := run_program_sources image entry present
  have metadata := xorrot_metadata source.fields encoding
  have flags := decoder_selectors decoderSize core (custom_field_bounds source.fields).2.1 query
  have zero (i : Fin 19) (bit : i.val ≠ 16) :
      w importedConstraintsDecoderColumns.flags[i] = 0 := by
    have flag := flags i
    rw [metadata.1] at flag
    have noBit : Nat.testBit 65536 i.val = false := by
      have bound := i.isLt
      interval_cases i.val
      all_goals first | exact False.elim (bit rfl) | decide
    simpa only [noBit, Bool.false_eq_true, if_false] using flag
  have selected : w 26 = 0 ∧ w 27 = 1 := by
    refine ⟨zero 15 (by decide), ?_⟩
    have flag := flags 16
    rw [metadata.1] at flag
    simpa [importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
  have other : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0 :=
    ⟨zero 10 (by decide), zero 11 (by decide), zero 12 (by decide), zero 13 (by decide)⟩
  have load : w 28 = 0 := zero 17 (by decide)
  have immediate : w 8 = 0 ∧ w 9 = 0 := by
    have lo := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query
    have hi := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query
    change w 8 = (entry.data.immediate.lo : ZMod p) at lo
    change w 9 = (entry.data.immediate.hi : ZMod p) at hi
    rw [metadata.1] at lo hi
    exact ⟨by simpa using lo, by simpa using hi⟩
  have funct3 : w 10 = (47 + input.rotation.val : Nat) := by
    have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query
    change w 10 = (entry.data.funct3 : ZMod p) at tag
    rw [metadata.1] at tag
    exact tag
  have modelCore := core
  rw [assumptions.setup] at modelCore
  have bytes := xorrot_operand_bytes (by dsimp [limbBase] at limbSize; omega)
    byteInverse modelCore selected other input.rotation funct3 load immediate
  have result := xorrot_destination (by omega) modelCore selected other input.rotation funct3
    (Control.leftWord w).toBitVec (Control.rightWord w).toBitVec bytes.1 bytes.2
  have leftWord : input.left = Control.leftWord w := by
    simpa [Control.leftWord, TriAdd.leftOperand, read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using mapping.words.left
  have oldWord : input.oldDestination = Control.rightWord w := by
    simpa [Control.rightWord, TriAdd.rightOperand, read_word, importedConstraintsMemoryPorts, WordColumns.evaluate] using mapping.words.oldDestination
  have destination : output.destination.toBitVec =
      (input.left.toBitVec ^^^ input.oldDestination.toBitVec).rotateRight (XorRotate.amount input.rotation) := by
    rw [leftWord, oldWord, mapping.words.destination]
    exact result
  have registers := register_reads limbSize core load query trace.memoryEpoch history
  have rs1 : (.Regidx entry.data.rs1 : SailRV32.regidx) = input.rs1 := by rw [metadata.1]
  have rd : (.Regidx entry.data.rs2 : SailRV32.regidx) = input.rd := by rw [metadata.1]
  rw [rs1, rd] at registers
  change run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok (Control.leftWord w).toBitVec input.before ∧
    run (SailRV32.Functions.rX_bits input.rd) input.before = .ok (Control.rightWord w).toBitVec input.before at registers
  rw [← leftWord, ← oldWord] at registers
  have pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before := by
    obtain ⟨newer, older, middle, permutation, ordered, writes, state⟩ := mapping.state
    rw [state, mapping.words.pc]
    exact retired_state_pc middle _
  have pcValue := native_query_pc_word limbSize query
  change Control.initialPC w = Word.ofBitVec entry.pc at pcValue
  have pc := pc_successor (by omega) core (accepted.active _ member) other
    (initial := input.pc) (final := output.pc)
    ⟨by rw [mapping.words.pc]; exact (ZMod.natCast_zmod_val _).symm,
      by rw [mapping.words.pc]; exact (ZMod.natCast_zmod_val _).symm,
      congrArg Word.lo mapping.words.finalPC, congrArg Word.hi mapping.words.finalPC⟩
    (by rw [mapping.words.pc, pcValue]; exact Word.ofBitVec_bound entry.pc)
  apply Sail.retire_of_destination pcRead pc.2.2
  let prepared := { input.before with regs := input.before.regs.insert .nextPC output.pc.toBitVec }
  have leftRead := Sail.rX_nextPC input.rs1 registers.1 (pc := output.pc.toBitVec)
  have oldRead := Sail.rX_nextPC input.rd registers.2 (pc := output.pc.toBitVec)
  obtain ⟨final, written⟩ := Sail.write_success input.rd output.destination.toBitVec prepared
  refine ⟨final, ?_, ?_⟩
  · simp only [XorRotate.execution]
    rw [run_bind_of_ok _ _ _ _ _ leftRead, run_bind_of_ok _ _ _ _ _ oldRead,
      ← destination, run_bind_of_ok _ _ _ _ _ written]
    rfl
  · rw [Sail.writeResult, run_bind_of_ok _ _ _ _ _ written]
    rfl

end Airbender.UnifiedReduced.Proofs
