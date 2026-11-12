module
public import Proven.Trace.RVPooledStep
public import Proven.Trace.RVPooledRow
public import Proven.ShiftBinop.RVTraceSoundness
public import Proven.ISA.RV.DecodeShape
public import Proven.Defs.Helpers.Memory.Ports
public import Proven.Defs.Helpers.Memory.RowEvents
public import Proven.Defs.Helpers.Memory.History
public import Proven.Defs.Helpers.Core.Word

@[expose] public section

/-! One shift/binop/REV8 row of a pooled trace is one `RV.exec` of its instruction (`RVPooledRowStep`), from the
    row's own RV history: the row calculation of `ShiftBinop.Proofs.rv_trace_soundness` (`rv_query_facts`,
    `rv_row_value`, `pc_successor`) with the operands and the destination write read off the history. For immediate
    forms and REV8 the second port reads x0, whose bounded read is the zero code. -/

namespace Airbender.Trace.Proofs
open Arithmetic ShiftBinop ShiftBinop.Proofs

theorem rv_shift_shape {i : RV.Instr} {d : DecoderData Unit} (fields : ShiftBinop.rvDecoderFields i = some d)
    (shape : RV.Shape i) (s : RV.State) : ∃ input : RVInput, input.before = s ∧ i = rvInstruction input := by
  cases i with
  | op op rd rs1 rs2 =>
    cases op <;> simp only [ShiftBinop.rvDecoderFields, reduceCtorEq] at fields
    · exact ⟨⟨.sll, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
    · exact ⟨⟨.xor, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
    · exact ⟨⟨.srl, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
    · exact ⟨⟨.sra, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
    · exact ⟨⟨.or, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
    · exact ⟨⟨.and, false, 0, 0, ⟨0, 0⟩, rs1, rs2, rd, 0, s⟩, rfl, rfl⟩
  | opImm op rd rs1 imm =>
    simp only [RV.Shape] at shape
    rcases shape with ⟨kind, x, rfl⟩ | ⟨kind, sh, rfl⟩
    · rcases kind with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [ShiftBinop.rvDecoderFields, reduceCtorEq] at fields
      · exact ⟨⟨.xor, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
      · exact ⟨⟨.or, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
      · exact ⟨⟨.and, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, x, s⟩, rfl, rfl⟩
    · have low : ((sh.zeroExtend 12).extractLsb' 0 5).zeroExtend 32 = sh.zeroExtend 32 := by
        apply BitVec.eq_of_toNat_eq
        have := sh.isLt
        simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
          Nat.shiftRight_zero]
        omega
      rcases kind with rfl | rfl | rfl
      · exact ⟨⟨.sll, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, sh.zeroExtend 12, s⟩, rfl, by simp only [rvInstruction, low]⟩
      · exact ⟨⟨.srl, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, sh.zeroExtend 12, s⟩, rfl, by simp only [rvInstruction, low]⟩
      · exact ⟨⟨.sra, true, 0, 0, ⟨0, 0⟩, rs1, 0, rd, sh.zeroExtend 12, s⟩, rfl, by simp only [rvInstruction, low]⟩
  | rev8 rd rs1 => exact ⟨⟨.rev8, false, 0, 0, ⟨0, 0⟩, rs1, 0, rd, 0, s⟩, rfl, rfl⟩
  | _ => simp [ShiftBinop.rvDecoderFields] at fields

theorem rv_shift_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {before after : RV.State} {entry : RVPooledProgramEntry} {i : RV.Instr}
    (facts : RVPooledRowFacts trace initial cells ⟨.shiftBinop, w⟩ before after entry)
    (fields : rvPooledDecoderFields i = some entry.data) (shape : RV.Shape i) :
    RVPooledRowStep ⟨.shiftBinop, w⟩ before after i := by
  have core := Verification.holds_of_sublist facts.constraints
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  obtain ⟨d, fd, data⟩ := (rv_pooled_fields_family fields).2.2.2.1 facts.family
  obtain ⟨input, rfl, rfl⟩ := rv_shift_shape fd shape before
  rw [rv_fields fd] at data
  obtain ⟨selected, funct3, immediateLo, immediateHi, pcWord, rs1Query, rs2Query, rdQuery⟩ :=
    rv_query_facts hp core data facts.query
  -- Operands and destination from the row's history.
  have shape : (⟨.shiftBinop, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.shiftBinop, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    rfl
  have history := facts.history
  dsimp only [rowEvents] at history
  rw [shape] at history
  obtain ⟨left, right, written⟩ := rv_register_row (by omega) trace.memoryEpoch
    (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts])
    rfl rfl rfl rs1Query rs2Query rdQuery history
  have outputWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 31).val (w 32).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  -- For immediate forms and REV8 the second port reads x0: its bounded read is the zero code.
  have zeroRead : (input.immediate || input.operation = .rev8) = true →
      importedConstraintsMemoryPorts[1].readCode w = 0 := by
    intro ignored
    have bound := facts.readBounds importedConstraintsMemoryPorts[1]
      (by change importedConstraintsMemoryPorts[1] ∈ importedConstraintsMemoryPorts
          simp [importedConstraintsMemoryPorts])
    apply rv_zero_code bound
    rw [← right, ite_eq_left ignored]
    rfl
  have result := rv_row_value (by omega) core input.operation input.immediate input.encodedImmediate
    selected funct3 immediateLo immediateHi zeroRead
  -- PC successor.
  have pcNext := pc_successor (by omega) arithmeticInverse core
    (initial := Word.ofBitVec entry.pc) (final := Word.mk (w 13).val (w 14).val)
    ⟨by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm,
     by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ (Word.ofBitVec_bound entry.pc)
  have finish : (⟨.shiftBinop, w⟩ : Row p PooledFamily).finish.word.toBitVec = input.before.pc + 4 := by
    change (Word.mk (w 13).val (w 14).val).toBitVec = _
    rw [pcNext.2.2, Word.ofBitVec_roundtrip, facts.pc]
  have value : rvValue input.operation input.immediate input.encodedImmediate
      (input.before.getReg input.rs1) (input.before.getReg input.rs2) =
      memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) := by
    rw [outputWord, result, left, ← right]
    by_cases ignored : (input.immediate || input.operation = .rev8) = true
    · exact rv_value_second _ _ _ _ ignored
    · rw [ite_eq_right ignored]
  refine ⟨_, rv_exec_row _ _, ?_⟩
  rw [value]
  exact rv_register_next written finish

end Airbender.Trace.Proofs
