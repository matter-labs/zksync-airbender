module
public import Slop.Trace.RVPooledStep
public import Slop.Trace.RVPooledRow
public import Slop.Trace.RVPooled.Arithmetic
public import Slop.AddSub.RVTraceSoundness
public import Slop.ISA.RV.DecodeShape

@[expose] public section

/-! One ADD/SUB-family row of a pooled trace whose metadata is the standard table's is one `RV.exec` of its
    instruction (`RVPooledRowStep`), from the row's own RV history:

    - every row reads its operand registers on ports 0/1, writes its destination register on port 2 and advances the
      PC by four (`rv_addsub_frame`);
    - a NOP row (an arithmetic write to x0 or a discarded load) writes x0 (`rv_nop_exec`);
    - ADD/SUB/ADDI/LUI/AUIPC with `rd ≠ x0`: the row calculation of `AddSub.Proofs.rv_trace_soundness`
      (`result_word_row` with the decoder contract from the entry's data). -/

namespace Airbender.Trace.Proofs
open Arithmetic AddSub AddSub.Proofs

/-- What every ADD/SUB-family row gives, for any metadata `d` of its entry: the operand registers are the read
    words, the history writes the destination register with the output word, and the PC advances by four. -/
theorem rv_addsub_frame {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {before after : RV.State} {entry : RVPooledProgramEntry}
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ before after entry)
    {d : DecoderData} (dataEq : entry.data = d.mapFamily pooledArithmeticFamily) :
    before.getReg d.rs1 = (Word.mk (w 25).val (w 26).val).toBitVec ∧
      before.getReg d.rs2 = (Word.mk (w 29).val (w 30).val).toBitVec ∧
      RV.Same after (before.setReg d.rd (Word.mk (w 33).val (w 34).val).toBitVec) ∧
      (⟨.addSub, w⟩ : Row p PooledFamily).finish.word.toBitVec = before.pc + 4 := by
  have core := Verification.holds_of_sublist facts.constraints
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  have beforePC := facts.pc
  have history := facts.history
  have query := facts.query
  obtain ⟨pc, entryBits, entryData⟩ := entry
  change entryData = d.mapFamily pooledArithmeticFamily at dataEq
  subst dataEq
  change before.pc = pc at beforePC
  have query0 : (⟨.addSub, w⟩ : Row p).decoderQuery = (⟨pc, entryBits, d⟩ : RVProgramEntry).query := query
  have pcWord := rv_native_query_pc_word limbSize query0
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec pc at pcWord
  have rs1Query := congrArg (fun q : Vector (ZMod p) 9 => q[2]) query0
  change w 5 = (d.rs1.toNat : ZMod p) at rs1Query
  have rs2Query := congrArg (fun q : Vector (ZMod p) 9 => q[3]) query0
  change w 6 = (d.rs2.toNat : ZMod p) at rs2Query
  have rdQuery := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query0
  change w 7 = (d.rd.toNat : ZMod p) at rdQuery
  have shape : (⟨.addSub, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.addSub, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    rfl
  dsimp only [rowEvents] at history
  rw [shape] at history
  obtain ⟨left, right, written⟩ := rv_register_row (by omega) trace.memoryEpoch
    (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts])
    rfl rfl rfl rs1Query rs2Query rdQuery history
  have leftWord : memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) =
      (Word.mk (w 25).val (w 26).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rightWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 29).val (w 30).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have outputWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 33).val (w 34).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  have pcNext := pc_successor (by omega) arithmeticInverse core
    (initial := Word.ofBitVec pc) (final := Word.mk (w 19).val (w 20).val)
    ⟨by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm,
     by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ (Word.ofBitVec_bound pc)
  refine ⟨left.trans leftWord, right.trans rightWord, outputWord ▸ written, ?_⟩
  change (Word.mk (w 19).val (w 20).val).toBitVec = _
  rw [pcNext.2.2, Word.ofBitVec_roundtrip, beforePC]

/-- A NOP row: the instruction only advances the PC, and the history writes x0. -/
theorem rv_nop_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {before after : RV.State} {entry : RVPooledProgramEntry} {i : RV.Instr}
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ before after entry)
    (dataEq : entry.data = rvNopData.mapFamily pooledArithmeticFamily)
    (exec : ∃ next, RV.exec before i = some next ∧ RV.Same next before.nextInstr) :
    RVPooledRowStep ⟨.addSub, w⟩ before after i := by
  obtain ⟨-, -, written, finish⟩ := rv_addsub_frame hp inverse facts dataEq
  obtain ⟨next, step, same⟩ := exec
  exact ⟨next, step, same.trans (rv_state_next (written.trans (rv_same_set_zero _ _)) rfl finish)⟩

/-- ADD/SUB/ADDI/LUI/AUIPC with `rd ≠ x0`. -/
theorem rv_arithmetic_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {after : RV.State} {entry : RVPooledProgramEntry} (input : RVInput)
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ input.before after entry)
    (fields : rvDecoderFields (rvInstruction input) = some (rvData input))
    (dataEq : entry.data = (rvData input).mapFamily pooledArithmeticFamily)
    (nonzero : input.rd ≠ 0)
    (rowLeft : input.row.left = Word.mk (w 25).val (w 26).val)
    (rowRight : input.row.right = Word.mk (w 29).val (w 30).val)
    (rowImmediate : input.row.immediate = Word.mk (w 8).val (w 9).val)
    (rowPC : input.row.pc = Word.mk (w 0).val (w 1).val) :
    RVPooledRowStep ⟨.addSub, w⟩ input.before after (rvInstruction input) := by
  have core := Verification.holds_of_sublist facts.constraints
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨leftValue, rightValue, written, finish⟩ := rv_addsub_frame hp inverse facts dataEq
  have rdData : (rvData input).rd = input.rd := by
    obtain ⟨⟨opcode, l, r, imm, pcw⟩, rs1, rs2, rd, e, u, before⟩ := input
    cases opcode <;> simp [rvData, arithmeticFields, show rd ≠ 0#5 from nonzero]
  rw [rdData] at written
  have fieldBounds := rv_decoder_field_bounds fields
  have query := facts.query
  have beforePC := facts.pc
  obtain ⟨pc, entryBits, entryData⟩ := entry
  change entryData = (rvData input).mapFamily pooledArithmeticFamily at dataEq
  subst dataEq
  change input.before.pc = pc at beforePC
  have query0 : (⟨.addSub, w⟩ : Row p).decoderQuery =
      (⟨pc, entryBits, rvData input⟩ : RVProgramEntry).query := query
  have pcWord := rv_native_query_pc_word limbSize query0
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec pc at pcWord
  have pcBounds : input.row.pc.Bounded := by
    rw [rowPC, pcWord]
    exact Word.ofBitVec_bound pc
  have rowPCBits : input.row.pc.toBitVec = pc := by
    rw [rowPC, pcWord, Word.ofBitVec_roundtrip]
  -- Operand bounds.
  have readBound (k : Fin 2) := facts.readBounds importedConstraintsMemoryPorts[k]
    (by change importedConstraintsMemoryPorts[k] ∈ importedConstraintsMemoryPorts
        fin_cases k <;> simp [importedConstraintsMemoryPorts])
  have bounds : (Word.mk (w 25).val (w 26).val).Bounded ∧ (Word.mk (w 29).val (w 30).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using And.intro (readBound 0) (readBound 1)
  rw [← rowLeft] at leftValue
  rw [← rowRight] at rightValue
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
  have flags := rv_row_query_selectors_of_bound limbSize trace.rom.wordMemory facts.constraints mask query0
  change ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] =
    if (rvData input).mask.testBit i.val then 1 else 0 at flags
  -- The row calculation.
  let output : Circuit.Output := ⟨⟨(w 33).val, (w 34).val⟩, ⟨(w 19).val, (w 20).val⟩⟩
  have rowMapping : RowWordMappingRow input.row input.rd output w := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · rw [rowLeft, ZMod.natCast_zmod_val]
    · rw [rowLeft, ZMod.natCast_zmod_val]
    · rw [rowRight, ZMod.natCast_zmod_val]
    · rw [rowRight, ZMod.natCast_zmod_val]
    · rw [rowImmediate, ZMod.natCast_zmod_val]
    · rw [rowImmediate, ZMod.natCast_zmod_val]
    · rw [rowPC, ZMod.natCast_zmod_val]
    · rw [rowPC, ZMod.natCast_zmod_val]
    · have q := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query0
      change w 7 = ((rvData input).rd.toNat : ZMod p) at q
      rw [q, rdData]
  have result : output.destination.toBitVec = match input.row.opcode with
      | .add => input.row.left.toBitVec + input.row.right.toBitVec
      | .addi => input.row.left.toBitVec + input.row.immediate.toBitVec
      | .sub => input.row.left.toBitVec - input.row.right.toBitVec
      | .lui => input.row.immediate.toBitVec
      | .auipc => input.row.pc.toBitVec + input.row.immediate.toBitVec := by
    have hz := nonzero
    have nz : input.rd ≠ 0#5 := hz
    have contract : DecoderContractRow input.row input.rd w := by
      constructor
      · exact facts.active
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
  change (Word.mk (w 33).val (w 34).val).toBitVec = _ at result
  -- Per opcode: `RV.exec` and agreement with the history.
  obtain ⟨⟨opcode, l, r, imm, pcw⟩, rs1, rs2, rd, e, u, before⟩ := input
  have nz : rd ≠ 0#5 := nonzero
  dsimp only at leftValue rightValue immediateValue rowPCBits result beforePC written finish ⊢
  cases opcode
  · have v : before.getReg rs1 + before.getReg rs2 = (Word.mk (w 33).val (w 34).val).toBitVec := by
      simp only [rvData, arithmeticFields, nonzero, ↓reduceIte] at leftValue rightValue
      rw [result, leftValue, rightValue]
    refine ⟨(before.setReg rd (before.getReg rs1 + before.getReg rs2)).nextInstr, rfl, ?_⟩
    rw [v]
    exact rv_register_next written finish
  · have v : before.getReg rs1 + e.signExtend 32 = (Word.mk (w 33).val (w 34).val).toBitVec := by
      simp only [rvData, arithmeticFields, nonzero, ↓reduceIte] at leftValue immediateValue
      rw [result, leftValue, immediateValue, Word.ofBitVec_roundtrip]
    refine ⟨(before.setReg rd (before.getReg rs1 + e.signExtend 32)).nextInstr, rfl, ?_⟩
    rw [v]
    exact rv_register_next written finish
  · have v : before.getReg rs1 - before.getReg rs2 = (Word.mk (w 33).val (w 34).val).toBitVec := by
      simp only [rvData, arithmeticFields, nonzero, ↓reduceIte] at leftValue rightValue
      rw [result, leftValue, rightValue]
    refine ⟨(before.setReg rd (before.getReg rs1 - before.getReg rs2)).nextInstr, rfl, ?_⟩
    rw [v]
    exact rv_register_next written finish
  · have v : (u ++ 0#12 : BitVec 32) = (Word.mk (w 33).val (w 34).val).toBitVec := by
      simp only [rvData, arithmeticFields, nonzero, ↓reduceIte] at immediateValue
      rw [result, immediateValue, Word.ofBitVec_roundtrip]
    refine ⟨(before.setReg rd (u ++ 0#12)).nextInstr, rfl, ?_⟩
    rw [v]
    exact rv_register_next written finish
  · have v : before.pc + (u ++ 0#12 : BitVec 32) = (Word.mk (w 33).val (w 34).val).toBitVec := by
      simp only [rvData, arithmeticFields, nonzero, ↓reduceIte] at immediateValue
      rw [result, immediateValue, Word.ofBitVec_roundtrip, rowPCBits, beforePC]
    refine ⟨(before.setReg rd (before.pc + (u ++ 0#12))).nextInstr, rfl, ?_⟩
    rw [v]
    exact rv_register_next written finish

/-- Any ADD/SUB-family row with standard metadata. -/
theorem rv_addsub_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {before after : RV.State} {entry : RVPooledProgramEntry} {i : RV.Instr}
    (facts : RVPooledRowFacts trace initial cells ⟨.addSub, w⟩ before after entry)
    {d : DecoderData} (fd : Trace.rvDecoderFields i = some d)
    (dataEq : entry.data = d.mapFamily pooledArithmeticFamily) (shape : RV.Shape i) :
    RVPooledRowStep ⟨.addSub, w⟩ before after i := by
  have family : d.family = .addSub := by
    have tag := facts.family
    rw [dataEq] at tag
    cases hf : d.family <;> simp [DecoderData.mapFamily, pooledArithmeticFamily, hf] at tag ⊢
  have arithmetic (input : RVInput) (hb : input.before = before) (hi : i = rvInstruction input)
      (nonzero : input.rd ≠ 0) (rowLeft : input.row.left = Word.mk (w 25).val (w 26).val)
      (rowRight : input.row.right = Word.mk (w 29).val (w 30).val)
      (rowImmediate : input.row.immediate = Word.mk (w 8).val (w 9).val)
      (rowPC : input.row.pc = Word.mk (w 0).val (w 1).val) :
      RVPooledRowStep ⟨.addSub, w⟩ before after i := by
    subst hb hi
    have same : d = rvData input := Option.some.inj (fd.symm.trans (rv_decoder_fields input))
    subst same
    exact rv_arithmetic_row_step hp inverse input facts (rv_decoder_fields input) dataEq nonzero
      rowLeft rowRight rowImmediate rowPC
  let L : Word := ⟨(w 25).val, (w 26).val⟩
  let R : Word := ⟨(w 29).val, (w 30).val⟩
  let I : Word := ⟨(w 8).val, (w 9).val⟩
  let P : Word := ⟨(w 0).val, (w 1).val⟩
  rcases rv_arithmetic_cases fd with rfl | ⟨-, rd, nonzero, cases⟩ | ⟨tag, -⟩
  · exact rv_nop_row_step hp inverse facts dataEq (rv_nop_exec before fd)
  · rcases cases with ⟨rs1, rs2, rfl | rfl⟩ | ⟨rs1, imm, rfl⟩ | ⟨imm, rfl | rfl⟩
    · exact arithmetic ⟨⟨.add, L, R, I, P⟩, rs1, rs2, rd, 0, 0, before⟩ rfl rfl nonzero rfl rfl rfl rfl
    · exact arithmetic ⟨⟨.sub, L, R, I, P⟩, rs1, rs2, rd, 0, 0, before⟩ rfl rfl nonzero rfl rfl rfl rfl
    · obtain ⟨x, rfl⟩ : ∃ x : BitVec 12, imm = x.signExtend 32 := by
        simp only [RV.Shape] at shape
        rcases shape with ⟨-, x, hx⟩ | ⟨kind, -⟩
        · exact ⟨x, hx⟩
        · rcases kind with h | h | h <;> cases h
      exact arithmetic ⟨⟨.addi, L, R, I, P⟩, rs1, 0, rd, x, 0, before⟩ rfl rfl nonzero rfl rfl rfl rfl
    · obtain ⟨u, rfl⟩ := shape
      exact arithmetic ⟨⟨.lui, L, R, I, P⟩, 0, 0, rd, 0, u, before⟩ rfl rfl nonzero rfl rfl rfl rfl
    · obtain ⟨u, rfl⟩ := shape
      exact arithmetic ⟨⟨.auipc, L, R, I, P⟩, 0, 0, rd, 0, u, before⟩ rfl rfl nonzero rfl rfl rfl rfl
  · rw [tag] at family
    cases family

end Airbender.Trace.Proofs
