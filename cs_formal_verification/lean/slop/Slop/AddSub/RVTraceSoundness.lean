import Human.Circuits.AddSub.RVTheorems
import Slop.AddSub.RVDecoder
import Slop.AddSub.RVRowPosition
import Slop.AddSub.PC
import Slop.AddSub
import Slop.Trace.RVValues
import Slop.Trace.RVRom
import Slop.Trace.RVFetch

/-! RV32 AddSub soundness (`RVSoundnessClaim`), on the RV route: no Sail state, interpreter or `Configured` fact.

    - Fetch/step: the row's program entry (`RVTraceMapping.instruction`) is an aligned ROM word of the starting memory
      (`rvProgram_entry_fetch`); the row's pre-state has the entry's PC (decoder query) and the starting ROM bytes
      (`rvWriteHistory_rom`), so `RV.step` executes `rvInstruction input` (`rv_step_fetch`).
    - Result: `result_word_row` (row-level calculation) from the decoder contract (selectors and preprocessing from the
      entry's data `rvData`, a function of the instruction datatype), the operand bounds (`rv_pooled_value_bounds`) and
      the operand registers (`rv_addsub_row_position`).
    - PC: `pc_successor`. -/

namespace Airbender.AddSub.Proofs
open Arithmetic Trace Trace.Proofs

/-- Register/PC agreement of one step that writes `x` to `rd` with the claimed post-state. -/
private theorem same_of_result (s : RV.State) (rd : RV.Reg) (x out pc : BitVec 32)
    (value : rd ≠ 0 → x = out) (hpc : s.pc + 4 = pc) :
    RV.Same (s.setReg rd x).nextInstr ((s.setReg rd out).setPC pc) := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simpa [RV.State.nextInstr, RV.State.setPC, RV.State.setReg] using hpc
  · intro i
    simp only [RV.State.getReg, RV.State.nextInstr, RV.State.setPC, RV.State.setReg]
    by_cases hi : i = 0
    · simp [hi]
    · by_cases hr : i = rd
      · subst hr
        simp [value hi]
      · simp [hr]

theorem rv_trace_soundness : RVSoundnessClaim := by
  intro p _ hp inverse trace initial cells program assumptions input output w relation
  obtain ⟨⟨accepted, decoded, member⟩, mapping⟩ := relation
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints) importedConstraintsTimestampLookups)
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  -- The row's program entry: its bytes decode to the row's instruction, and its data is `rvData input`.
  obtain ⟨entry, present, _, query, decodes⟩ := mapping.instruction
  obtain ⟨guard, bits, i, decodedI, instruction, projection⟩ :=
    rvProgram_entry_fetch programImage entry present
  have hi : i = rvInstruction input := Option.some.inj (decodedI.symm.trans decodes)
  subst hi
  rw [rv_pooled_fields] at projection
  obtain ⟨pc, entryBits, entryInstruction, data⟩ := entry
  have dataEq : data = (rvData input).mapFamily pooledArithmeticFamily := (Option.some.inj projection).symm
  subst dataEq
  change entryInstruction = Airbender.toSail (rvInstruction input) at instruction
  change entryBits = RV.read initial.mem pc 4 at bits
  change pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0 at guard
  change RV.decode entryBits = some (rvInstruction input) at decodes
  have fields0 : decoderFields (⟨pc, entryBits, entryInstruction, rvData input⟩ : ProgramEntry).instruction =
      some (⟨pc, entryBits, entryInstruction, rvData input⟩ : ProgramEntry).data := by
    change decoderFields entryInstruction = some (rvData input)
    rw [instruction]
    exact rv_decoder_fields input
  have query0 : (⟨.addSub, w⟩ : Row p).decoderQuery =
      (⟨pc, entryBits, entryInstruction, rvData input⟩ : ProgramEntry).query := query
  -- Fetch/step: PC and ROM bytes of the pre-state.
  have pcWord := native_query_pc_word limbSize query0
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec pc at pcWord
  obtain ⟨_, _, middle, _, _, history, atState⟩ := mapping.state
  have beforePC : input.before.pc = pc := by
    rw [atState]
    change (Word.mk (w 0).val (w 1).val).toBitVec = pc
    rw [pcWord, Word.ofBitVec_roundtrip]
  have agree : ∀ a : RV.Word, a.toNat < RV.ROM_END → input.before.mem a = initial.mem a := by
    intro a rom
    rw [atState]
    exact rvWriteHistory_rom history a rom
  obtain ⟨_, step⟩ := rv_step_fetch input.before initial agree pc beforePC guard
  rw [← bits, decodes] at step
  -- PC successor.
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have rowPC : input.row.pc = Word.mk (w 0).val (w 1).val :=
    congrArg₂ Word.mk mapping.words.pcLo mapping.words.pcHi
  have pcBounds : input.row.pc.Bounded := by
    rw [rowPC, pcWord]
    exact Word.ofBitVec_bound pc
  have rowPCBits : input.row.pc.toBitVec = pc := by
    rw [rowPC, pcWord, Word.ofBitVec_roundtrip]
  have pcMapping : PCMapping input.row.pc output.pc w := by
    rw [rowPC]
    exact ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm,
      mapping.words.finalPCLo, mapping.words.finalPCHi⟩
  have pcNext := pc_successor (by omega) arithmeticInverse core pcMapping pcBounds
  have hpc : input.before.pc + 4 = output.pc.toBitVec := by
    rw [pcNext.2.2, rowPCBits, beforePC]
  -- Operand bounds.
  have readBounds := (Trace.RVValues.rv_pooled_value_bounds (by omega) inverse accepted
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
  -- Operand registers.
  have rs1Query := congrArg (fun q : Vector (ZMod p) 9 => q[2]) query0
  change w 5 = ((rvData input).rs1.toNat : ZMod p) at rs1Query
  have rs2Query := congrArg (fun q : Vector (ZMod p) 9 => q[3]) query0
  change w 6 = ((rvData input).rs2.toNat : ZMod p) at rs2Query
  have regs := rv_addsub_row_position clockSize inverse accepted assumptions decoded member mapping.state
    (rvData input).rs1 (rvData input).rs2 rs1Query rs2Query
  have leftWord : memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) =
      (Word.mk (w 25).val (w 26).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rightWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 29).val (w 30).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rowLeft : input.row.left = Word.mk (w 25).val (w 26).val :=
    congrArg₂ Word.mk mapping.words.leftLo mapping.words.leftHi
  have rowRight : input.row.right = Word.mk (w 29).val (w 30).val :=
    congrArg₂ Word.mk mapping.words.rightLo mapping.words.rightHi
  have rowImmediate : input.row.immediate = Word.mk (w 8).val (w 9).val :=
    congrArg₂ Word.mk mapping.words.immediateLo mapping.words.immediateHi
  have leftValue : input.before.getReg (rvData input).rs1 = input.row.left.toBitVec := by
    rw [regs.1, leftWord, rowLeft]
  have rightValue : input.before.getReg (rvData input).rs2 = input.row.right.toBitVec := by
    rw [regs.2, rightWord, rowRight]
  -- Immediate and selectors from the decoder query.
  have immediateValue := query_immediate_value limbSize fields0 query0
  change Word.mk (w 8).val (w 9).val = (rvData input).immediate at immediateValue
  rw [← rowImmediate] at immediateValue
  have immediateBound := query_immediate limbSize fields0 query0
  change (Word.mk (w 8).val (w 9).val).Bounded at immediateBound
  rw [← rowImmediate] at immediateBound
  have mask : (rvData input).mask < 512 := by
    unfold rvData
    split <;> (unfold arithmeticFields; split <;> simp)
  have flags := row_query_selectors_of_bound limbSize trace.rom.wordMemory (accepted.constraints _ member)
    mask query0
  change ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] =
    if (rvData input).mask.testBit i.val then 1 else 0 at flags
  -- The row calculation.
  have rowMapping : RowWordMappingRow input.row input.rd output w := by
    have m := mapping.words
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, m.destinationIndex, m.outputLo, m.outputHi, m.finalPCLo,
      m.finalPCHi⟩
    · rw [m.leftLo, ZMod.natCast_zmod_val]
    · rw [m.leftHi, ZMod.natCast_zmod_val]
    · rw [m.rightLo, ZMod.natCast_zmod_val]
    · rw [m.rightHi, ZMod.natCast_zmod_val]
    · rw [m.immediateLo, ZMod.natCast_zmod_val]
    · rw [m.immediateHi, ZMod.natCast_zmod_val]
    · rw [m.pcLo, ZMod.natCast_zmod_val]
    · rw [m.pcHi, ZMod.natCast_zmod_val]
  have result (hz : input.rd ≠ 0) : output.destination.toBitVec = match input.row.opcode with
      | .add => input.row.left.toBitVec + input.row.right.toBitVec
      | .addi => input.row.left.toBitVec + input.row.immediate.toBitVec
      | .sub => input.row.left.toBitVec - input.row.right.toBitVec
      | .lui => input.row.immediate.toBitVec
      | .auipc => input.row.pc.toBitVec + input.row.immediate.toBitVec := by
    have nz : input.rd ≠ 0#5 := hz
    have contract : DecoderContractRow input.row input.rd w := by
      constructor
      · exact accepted.active _ member
      · have flag := flags ⟨0, by decide⟩
        cases hop : input.row.opcode <;>
          simpa [rvData, arithmeticFields, hop, nz, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
      · have flag := flags ⟨1, by decide⟩
        cases hop : input.row.opcode <;>
          simpa [rvData, arithmeticFields, hop, nz, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
      · intro k lower upperBound
        have flag := flags ⟨k - 10, by omega⟩
        interval_cases k
        all_goals cases hop : input.row.opcode
        all_goals simpa [rvData, arithmeticFields, hop, nz, Nat.testBit, Nat.shiftRight_eq_div_pow] using flag
      · unfold PreprocessingRow
        rw [if_neg hz]
        cases hop : input.row.opcode
        · simpa [rvData, arithmeticFields, hop, nz, Word.ofBitVec] using immediateValue
        · rw [rowRight]
          apply Word.eq_zero_of_bounded bounds.2
          rw [← rowRight, ← rightValue]
          simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
        · simpa [rvData, arithmeticFields, hop, nz, Word.ofBitVec] using immediateValue
        · constructor
          · rw [rowLeft]
            apply Word.eq_zero_of_bounded bounds.1
            rw [← rowLeft, ← leftValue]
            simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
          · rw [rowRight]
            apply Word.eq_zero_of_bounded bounds.2
            rw [← rowRight, ← rightValue]
            simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
        · constructor
          · rw [rowLeft]
            apply Word.eq_zero_of_bounded bounds.1
            rw [← rowLeft, ← leftValue]
            simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
          · rw [rowRight]
            apply Word.eq_zero_of_bounded bounds.2
            rw [← rowRight, ← rightValue]
            simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
    have inputBounds : InputBounds input.row :=
      ⟨rowLeft ▸ bounds.1, rowRight ▸ bounds.2, immediateBound⟩
    exact result_word_row (by omega) core contract hz inputBounds pcBounds rowMapping
  -- Per opcode: `RV.step` and agreement with the claimed post-state.
  obtain ⟨⟨opcode, l, r, imm, pcw⟩, rs1, rs2, rd, e, u, before⟩ := input
  dsimp only at step hpc leftValue rightValue immediateValue rowPCBits result beforePC
  cases opcode
  · refine ⟨(before.setReg rd (before.getReg rs1 + before.getReg rs2)).nextInstr, step.trans rfl,
      same_of_result _ _ _ _ _ ?_ hpc⟩
    intro hz
    have nz : rd ≠ 0#5 := hz
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at leftValue rightValue
    rw [result hz, leftValue, rightValue]
  · refine ⟨(before.setReg rd (before.getReg rs1 + e.signExtend 32)).nextInstr, step.trans rfl,
      same_of_result _ _ _ _ _ ?_ hpc⟩
    intro hz
    have nz : rd ≠ 0#5 := hz
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at leftValue immediateValue
    rw [result hz, leftValue, immediateValue, Word.ofBitVec_roundtrip]
  · refine ⟨(before.setReg rd (before.getReg rs1 - before.getReg rs2)).nextInstr, step.trans rfl,
      same_of_result _ _ _ _ _ ?_ hpc⟩
    intro hz
    have nz : rd ≠ 0#5 := hz
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at leftValue rightValue
    rw [result hz, leftValue, rightValue]
  · refine ⟨(before.setReg rd (u ++ 0#12)).nextInstr, step.trans rfl,
      same_of_result _ _ _ _ _ ?_ hpc⟩
    intro hz
    have nz : rd ≠ 0#5 := hz
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at immediateValue
    rw [result hz, immediateValue, Word.ofBitVec_roundtrip]
  · refine ⟨(before.setReg rd (before.pc + (u ++ 0#12))).nextInstr, step.trans rfl,
      same_of_result _ _ _ _ _ ?_ hpc⟩
    intro hz
    have nz : rd ≠ 0#5 := hz
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at immediateValue
    rw [result hz, immediateValue, Word.ofBitVec_roundtrip, rowPCBits, beforePC]

theorem babyBear_rv_trace_soundness : BabyBearRVSoundnessClaim := by
  intro trace initial cells program assumptions input output w relation
  exact rv_trace_soundness (p := babyBearModulus) (by decide) (by decide) trace initial cells program
    assumptions input output w relation

end Airbender.AddSub.Proofs
