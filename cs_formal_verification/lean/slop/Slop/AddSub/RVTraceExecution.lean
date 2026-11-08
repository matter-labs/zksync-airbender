module
public import Slop.Trace.RVFamilySelectors
public import Slop.AddSub.RVDecoder
public import Slop.AddSub.PC
public import Slop.AddSub
public import Slop.Trace.RVFamilyTrace
public import Slop.ISA.RV.DecodeShape
public import Slop.ISA.RV.Step

@[expose] public section

/-! One ADD/SUB-family row of the two-family (ADD/SUB + word memory) trace on the RV route: one `RV.exec` of its
    entry's instruction, agreeing with the row's RV history and final PC (`rv_row_step`). A row whose entry writes x0
    is the NOP row (`rv_decoder_zero_nop`), whatever pure instruction or load it came from (`rv_nop_exec`); otherwise
    the instruction is ADD/ADDI/SUB/LUI/AUIPC (`rv_fields_input`) and the row calculation is `result_word_row`, as in
    the per-row claim (`RVTraceSoundness.lean`), with the operand registers from the row's RV history. -/

namespace Airbender.AddSub.Proofs
open Arithmetic Trace Trace.Proofs

/-- An instruction whose ADD/SUB-family entry writes x0 only advances the PC (up to x0's stored value). -/
theorem rv_nop_exec (s : RV.State) {bits : RV.Word} {i : RV.Instr} {d : DecoderData}
    (decodes : RV.decode bits = some i) (fields : rvDecoderFields i = some d) (family : d.family = .addSub)
    (zero : d.rd = 0) : ∃ next, RV.exec s i = some next ∧ RV.Same next s.nextInstr := by
  have shape := RV.decode_shape decodes
  have setZero (v : RV.Word) : RV.Same (s.setReg 0 v).nextInstr s.nextInstr := (rv_same_set_zero s v).nextInstr
  cases i
  case op o rd rs1 rs2 =>
    by_cases hz : rd = 0#5
    · subst hz
      exact ⟨_, rfl, setZero _⟩
    · cases o <;> simp [rvDecoderFields, arithmeticFields, hz] at fields
      all_goals (subst fields; exact absurd zero hz)
  case opImm o rd rs1 imm =>
    by_cases hz : rd = 0#5
    · subst hz
      exact ⟨_, rfl, setZero _⟩
    · cases o <;> simp [rvDecoderFields, arithmeticFields, hz] at fields
      all_goals (subst fields; exact absurd zero hz)
  case lui rd imm =>
    by_cases hz : rd = 0#5
    · subst hz
      exact ⟨_, rfl, setZero _⟩
    · simp [rvDecoderFields, arithmeticFields, hz] at fields
      subst fields
      exact absurd zero hz
  case auipc rd imm =>
    by_cases hz : rd = 0#5
    · subst hz
      exact ⟨_, rfl, setZero _⟩
    · simp [rvDecoderFields, arithmeticFields, hz] at fields
      subst fields
      exact absurd zero hz
  case rev8 rd rs1 =>
    by_cases hz : rd = 0#5
    · subst hz
      exact ⟨_, rfl, setZero _⟩
    · simp [rvDecoderFields, hz] at fields
  case load n sg rd rs1 off =>
    by_cases hz : rd = 0#5
    · subst hz
      exact ⟨_, RV.exec_load_x0 s n sg rs1 off, RV.Same.refl _⟩
    · simp only [RV.Shape] at shape
      obtain ⟨width, _⟩ := shape
      rcases width with rfl | rfl | rfl
      all_goals cases sg
      all_goals simp [rvDecoderFields, hz] at fields
      subst fields
      cases family
  case store n rs2 rs1 off =>
    simp only [RV.Shape] at shape
    obtain ⟨width, _⟩ := shape
    rcases width with rfl | rfl | rfl
    all_goals simp [rvDecoderFields] at fields
    subst fields
    cases family
  all_goals simp [rvDecoderFields] at fields

/-- An ADD/SUB-family entry not writing x0 is the data of an RV input of the ADD/ADDI/SUB/LUI/AUIPC claim, with any
    row words. -/
theorem rv_fields_input {bits : RV.Word} {i : RV.Instr} {d : DecoderData}
    (decodes : RV.decode bits = some i) (fields : rvDecoderFields i = some d) (family : d.family = .addSub)
    (nonzero : d.rd ≠ 0) (left right immediate pc : Word) (s : RV.State) :
    ∃ input : RVInput, input.before = s ∧ input.row.left = left ∧ input.row.right = right ∧
      input.row.immediate = immediate ∧ input.row.pc = pc ∧ i = rvInstruction input ∧ d = rvData input := by
  have shape := RV.decode_shape decodes
  cases i
  case op o rd rs1 rs2 =>
    by_cases hz : rd = 0#5
    · subst hz
      cases o <;> simp [rvDecoderFields, arithmeticFields] at fields
      all_goals (subst fields; exact absurd rfl nonzero)
    · cases o <;> simp [rvDecoderFields, hz] at fields
      · exact ⟨⟨⟨.add, left, right, immediate, pc⟩, rs1, rs2, rd, 0, 0, s⟩, rfl, rfl, rfl, rfl, rfl, rfl,
          fields.symm⟩
      · exact ⟨⟨⟨.sub, left, right, immediate, pc⟩, rs1, rs2, rd, 0, 0, s⟩, rfl, rfl, rfl, rfl, rfl, rfl,
          fields.symm⟩
  case opImm o rd rs1 imm =>
    by_cases hz : rd = 0#5
    · subst hz
      cases o <;> simp [rvDecoderFields, arithmeticFields] at fields
      all_goals (subst fields; exact absurd rfl nonzero)
    · cases o <;> simp [rvDecoderFields, hz] at fields
      simp only [RV.Shape] at shape
      rcases shape with ⟨_, x, rfl⟩ | ⟨kind, _⟩
      · exact ⟨⟨⟨.addi, left, right, immediate, pc⟩, rs1, 0, rd, x, 0, s⟩, rfl, rfl, rfl, rfl, rfl, rfl,
          fields.symm⟩
      · simp at kind
  case lui rd imm =>
    simp only [RV.Shape] at shape
    obtain ⟨u, rfl⟩ := shape
    simp [rvDecoderFields] at fields
    exact ⟨⟨⟨.lui, left, right, immediate, pc⟩, 0, 0, rd, 0, u, s⟩, rfl, rfl, rfl, rfl, rfl, rfl, fields.symm⟩
  case auipc rd imm =>
    simp only [RV.Shape] at shape
    obtain ⟨u, rfl⟩ := shape
    simp [rvDecoderFields] at fields
    exact ⟨⟨⟨.auipc, left, right, immediate, pc⟩, 0, 0, rd, 0, u, s⟩, rfl, rfl, rfl, rfl, rfl, rfl, fields.symm⟩
  case rev8 rd rs1 =>
    by_cases hz : rd = 0#5
    · simp [rvDecoderFields, hz] at fields
      subst fields
      exact absurd rfl nonzero
    · simp [rvDecoderFields, hz] at fields
  case load n sg rd rs1 off =>
    simp only [RV.Shape] at shape
    obtain ⟨width, _⟩ := shape
    by_cases hz : rd = 0#5
    all_goals rcases width with rfl | rfl | rfl
    all_goals cases sg
    all_goals simp [rvDecoderFields, hz, arithmeticFields] at fields
    all_goals subst fields
    all_goals first
      | exact absurd rfl nonzero
      | cases family
  case store n rs2 rs1 off =>
    simp only [RV.Shape] at shape
    obtain ⟨width, _⟩ := shape
    rcases width with rfl | rfl | rfl
    all_goals simp [rvDecoderFields] at fields
    subst fields
    cases family
  all_goals simp [rvDecoderFields] at fields

/-- One ADD/SUB-family row is one `RV.exec` of its entry's instruction, agreeing with the row's RV history and final
    PC. -/
theorem rv_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    {setup : Table (ZMod p) (fields 9)} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      ((⟨.addSub, w⟩ : Row p).constraints setup))
    (active : w 4 = 1)
    {entry : RVProgramEntry} (family : entry.data.family = .addSub)
    (query : (⟨.addSub, w⟩ : Row p).decoderQuery = entry.query)
    {i : RV.Instr} (decodes : RV.decode entry.bits = some i) (fields : rvDecoderFields i = some entry.data)
    (leftBound : (Word.mk (w 25).val (w 26).val).Bounded) (rightBound : (Word.mk (w 29).val (w 30).val).Bounded)
    {cells : List Cell} (epoch : Nat) {before after : RV.State} (pc : before.pc = entry.pc)
    (history : RVHistory cells (rowEvents epoch (⟨.addSub, w⟩ : Row p)).reverse before after) :
    ∃ next, RV.exec before i = some next ∧
      RV.Same next { after with pc := (⟨.addSub, w⟩ : Row p).finish.word.toBitVec } := by
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  -- PC successor.
  have pcWord := rv_native_query_pc_word limbSize query
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at pcWord
  have pcBounds : (Word.mk (w 0).val (w 1).val).Bounded := by
    rw [pcWord]; exact Word.ofBitVec_bound entry.pc
  have pcNext := pc_successor (by omega) arithmeticInverse core
    (initial := Word.mk (w 0).val (w 1).val) (final := Word.mk (w 19).val (w 20).val)
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ pcBounds
  have rowPCBits : (Word.mk (w 0).val (w 1).val).toBitVec = before.pc := by
    rw [pcWord, Word.ofBitVec_roundtrip, pc]
  have finalPC : (⟨.addSub, w⟩ : Row p).finish.word.toBitVec = before.pc + 4 := by
    change (Word.mk (w 19).val (w 20).val).toBitVec = _
    rw [pcNext.2.2, rowPCBits]
  -- Operand registers and destination update, from the row's RV history.
  have indices := rv_native_query_indices limbSize query
  change (w 5).val = entry.data.rs1.toNat ∧ (w 6).val = entry.data.rs2.toNat ∧ (w 7).val = entry.data.rd.toNat
    at indices
  have shaped : RVHistory cells (nativeRowEvents epoch importedConstraintsTraceColumns
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1], importedConstraintsMemoryPorts[2]]
      w).reverse before after := history
  obtain ⟨left, right, written⟩ := rv_register_ports epoch (by simp [importedConstraintsMemoryPorts])
    (by simp [importedConstraintsMemoryPorts]) (a := 5) (b := 6) (c := 7)
    (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts])
    (by simp [importedConstraintsMemoryPorts]) indices.1 indices.2.1 indices.2.2 shaped
  have leftWord : memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) =
      (Word.mk (w 25).val (w 26).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rightWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 29).val (w 30).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have destinationWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 33).val (w 34).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  rw [leftWord] at left
  rw [rightWord] at right
  rw [destinationWord] at written
  by_cases zero : entry.data.rd = 0
  · -- The NOP row: the destination is x0.
    obtain ⟨next, exec, same⟩ := rv_nop_exec before decodes fields family zero
    rw [zero] at written
    exact ⟨next, exec, same.trans (rv_same_next (written.trans (rv_same_set_zero before _)) finalPC)⟩
  obtain ⟨input, rfl, rowLeft, rowRight, rowImmediate, rowPC, rfl, data⟩ :=
    rv_fields_input decodes fields family zero (Word.mk (w 25).val (w 26).val) (Word.mk (w 29).val (w 30).val)
      (Word.mk (w 8).val (w 9).val) (Word.mk (w 0).val (w 1).val) before
  rw [data] at zero left right written indices
  have hz : input.rd ≠ 0 := by
    intro h
    apply zero
    obtain ⟨⟨opcode, _, _, _, _⟩, _, _, rd, _, _, _⟩ := input
    change rd = 0 at h
    subst h
    cases opcode <;> simp [rvData, arithmeticFields]
  have rdIs : (rvData input).rd = input.rd := by
    obtain ⟨⟨opcode, _, _, _, _⟩, _, _, rd, _, _, _⟩ := input
    have nz : rd ≠ 0#5 := hz
    cases opcode <;> simp [rvData, arithmeticFields, nz]
  rw [rdIs] at written
  have fieldBounds := rv_decoder_field_bounds (rv_decoder_fields input)
  have query0 : (⟨.addSub, w⟩ : Row p).decoderQuery = (⟨entry.pc, entry.bits, rvData input⟩ : RVProgramEntry).query := by
    rw [query, ← data]
  -- Operand values.
  have leftValue : input.before.getReg (rvData input).rs1 = input.row.left.toBitVec := by rw [left, rowLeft]
  have rightValue : input.before.getReg (rvData input).rs2 = input.row.right.toBitVec := by rw [right, rowRight]
  have bounds : input.row.left.Bounded ∧ input.row.right.Bounded := by
    rw [rowLeft, rowRight]; exact ⟨leftBound, rightBound⟩
  -- Immediate and selectors from the decoder query.
  have immediateValue := rv_native_query_immediate_word limbSize fieldBounds.1 query0
  change Word.mk (w 8).val (w 9).val = (rvData input).immediate at immediateValue
  have immediateBound : (Word.mk (w 8).val (w 9).val).Bounded := by
    rw [immediateValue]
    exact fieldBounds.1
  rw [← rowImmediate] at immediateValue immediateBound
  have mask : (rvData input).mask < 512 := by
    have small := fieldBounds.2
    omega
  have flags := rv_row_query_selectors_of_bound limbSize setup constraints mask query0
  change ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] =
    if (rvData input).mask.testBit i.val then 1 else 0 at flags
  -- The row calculation.
  let output : Circuit.Output := ⟨⟨(w 33).val, (w 34).val⟩, ⟨(w 19).val, (w 20).val⟩⟩
  have rdQuery := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query0
  change w 7 = ((rvData input).rd.toNat : ZMod p) at rdQuery
  rw [rdIs] at rdQuery
  have rowMapping : RowWordMappingRow input.row input.rd output w := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rdQuery, rfl, rfl, rfl, rfl⟩
    · rw [rowLeft]; exact (ZMod.natCast_zmod_val _).symm
    · rw [rowLeft]; exact (ZMod.natCast_zmod_val _).symm
    · rw [rowRight]; exact (ZMod.natCast_zmod_val _).symm
    · rw [rowRight]; exact (ZMod.natCast_zmod_val _).symm
    · rw [rowImmediate]; exact (ZMod.natCast_zmod_val _).symm
    · rw [rowImmediate]; exact (ZMod.natCast_zmod_val _).symm
    · rw [rowPC]; exact (ZMod.natCast_zmod_val _).symm
    · rw [rowPC]; exact (ZMod.natCast_zmod_val _).symm
  have pcBoundsRow : input.row.pc.Bounded := by rw [rowPC]; exact pcBounds
  have result : output.destination.toBitVec = match input.row.opcode with
      | .add => input.row.left.toBitVec + input.row.right.toBitVec
      | .addi => input.row.left.toBitVec + input.row.immediate.toBitVec
      | .sub => input.row.left.toBitVec - input.row.right.toBitVec
      | .lui => input.row.immediate.toBitVec
      | .auipc => input.row.pc.toBitVec + input.row.immediate.toBitVec := by
    have nz : input.rd ≠ 0#5 := hz
    have contract : DecoderContractRow input.row input.rd w := by
      constructor
      · exact active
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
          apply Word.eq_zero_of_bounded rightBound
          rw [← rowRight, ← rightValue]
          simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
        · simpa [rvData, arithmeticFields, hop, nz, Word.ofBitVec] using immediateValue
        · constructor
          · rw [rowLeft]
            apply Word.eq_zero_of_bounded leftBound
            rw [← rowLeft, ← leftValue]
            simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
          · rw [rowRight]
            apply Word.eq_zero_of_bounded rightBound
            rw [← rowRight, ← rightValue]
            simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
        · constructor
          · rw [rowLeft]
            apply Word.eq_zero_of_bounded leftBound
            rw [← rowLeft, ← leftValue]
            simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
          · rw [rowRight]
            apply Word.eq_zero_of_bounded rightBound
            rw [← rowRight, ← rightValue]
            simp [rvData, arithmeticFields, hop, nz, RV.State.getReg]
    have inputBounds : InputBounds input.row := ⟨bounds.1, bounds.2, rowImmediate ▸ immediateBound⟩
    exact result_word_row (by omega) core contract hz inputBounds pcBoundsRow rowMapping
  have destination : output.destination.toBitVec = (Word.mk (w 33).val (w 34).val).toBitVec := by rfl
  rw [destination] at result
  -- Per opcode: `RV.exec` and agreement with the row's history.
  have rowPCIs : input.row.pc.toBitVec = input.before.pc := by rw [rowPC]; exact rowPCBits
  obtain ⟨⟨opcode, l, r, imm, pcw⟩, rs1, rs2, rd, e, u, s⟩ := input
  dsimp only at leftValue rightValue immediateValue rowPCIs result hz written finalPC ⊢
  have nz : rd ≠ 0#5 := hz
  cases opcode
  all_goals dsimp only at result
  · refine ⟨(s.setReg rd (s.getReg rs1 + s.getReg rs2)).nextInstr, rfl, rv_same_next ?_ finalPC⟩
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at leftValue rightValue
    rw [leftValue, rightValue, ← result]
    exact written
  · refine ⟨(s.setReg rd (s.getReg rs1 + e.signExtend 32)).nextInstr, rfl, rv_same_next ?_ finalPC⟩
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at leftValue immediateValue
    rw [leftValue, ← Word.ofBitVec_roundtrip (e.signExtend 32), ← immediateValue, ← result]
    exact written
  · refine ⟨(s.setReg rd (s.getReg rs1 - s.getReg rs2)).nextInstr, rfl, rv_same_next ?_ finalPC⟩
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at leftValue rightValue
    rw [leftValue, rightValue, ← result]
    exact written
  · refine ⟨(s.setReg rd (u ++ 0#12)).nextInstr, rfl, rv_same_next ?_ finalPC⟩
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at immediateValue
    rw [← Word.ofBitVec_roundtrip (u ++ 0#12), ← immediateValue, ← result]
    exact written
  · refine ⟨(s.setReg rd (s.pc + (u ++ 0#12))).nextInstr, rfl, rv_same_next ?_ finalPC⟩
    simp only [rvData, arithmeticFields, hz, ↓reduceIte] at immediateValue
    rw [← Word.ofBitVec_roundtrip (u ++ 0#12), ← immediateValue, ← rowPCIs, ← result]
    exact written

end Airbender.AddSub.Proofs
