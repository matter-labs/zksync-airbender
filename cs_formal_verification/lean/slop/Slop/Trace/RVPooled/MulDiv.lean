module
public import Slop.Trace.RVPooledStep
public import Slop.Trace.RVPooledRow
public import Slop.MulDiv.RVQuery
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Helpers.Memory.RowEvents
public import Slop.Defs.Circuits.MulDiv.Operation
public import Slop.Defs.Helpers.Memory.History
public import Slop.Defs.Helpers.Core.Word

@[expose] public section

/-! One MUL/MULHU/DIVU/REMU row of a pooled trace is one `RV.exec` of its instruction (`RVPooledRowStep`), from the
    row's own RV history: the row calculation of `MulDiv.Proofs.rv_trace_soundness` (`rv_query_facts`,
    `rv_row_result`, `pc_successor`) with the operands and the destination write read off the history
    (`rv_register_row`). -/

namespace Airbender.Trace.Proofs
open Arithmetic MulDiv MulDiv.Proofs

theorem rv_muldiv_shape {i : RV.Instr} {d : DecoderData Unit} (fields : MulDiv.rvDecoderFields i = some d)
    (s : RV.State) : ∃ input : RVInput, input.before = s ∧ i = rvInstruction input := by
  cases i with
  | op op rd rs1 rs2 =>
    cases op <;> simp only [MulDiv.rvDecoderFields, reduceCtorEq] at fields
    · exact ⟨⟨.mul, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, s⟩, rfl, rfl⟩
    · exact ⟨⟨.mulhu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, s⟩, rfl, rfl⟩
    · exact ⟨⟨.divu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, s⟩, rfl, rfl⟩
    · exact ⟨⟨.remu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, s⟩, rfl, rfl⟩
  | _ => simp [MulDiv.rvDecoderFields] at fields

theorem rv_muldiv_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {before after : RV.State} {entry : RVPooledProgramEntry} {i : RV.Instr}
    (facts : RVPooledRowFacts trace initial cells ⟨.mulDiv, w⟩ before after entry)
    (fields : rvPooledDecoderFields i = some entry.data) :
    RVPooledRowStep ⟨.mulDiv, w⟩ before after i := by
  have core := Verification.holds_of_sublist facts.constraints
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have arithmeticInverse : (-30720 : ZMod p) * 65536 = 1 := by
    calc
      (-30720 : ZMod p) * 65536 = (-3840 : ZMod p) * 524288 := by ring
      _ = 1 := inverse
  obtain ⟨d, fd, _⟩ := (rv_pooled_fields_family fields).2.2.1 facts.family
  obtain ⟨input, rfl, rfl⟩ := rv_muldiv_shape fd before
  obtain ⟨_, data⟩ := MulDiv.Proofs.rv_pooled_fields fields facts.family
  obtain ⟨selected, pcWord, rs1Query, rs2Query, rdQuery⟩ := rv_query_facts hp core data facts.query
  -- Operands and destination from the row's history.
  have shape : (⟨.mulDiv, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.mulDiv, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := by rfl
    rw [portsEq]
    rfl
  have history := facts.history
  dsimp only [rowEvents] at history
  rw [shape] at history
  obtain ⟨left, right, written⟩ := rv_register_row (by omega) trace.memoryEpoch
    (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts])
    rfl rfl rfl rs1Query rs2Query rdQuery history
  have leftWord : memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) =
      (Word.mk (w 20).val (w 21).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rightWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 24).val (w 25).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have outputWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 28).val (w 29).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  -- Left operand bound and the row calculation.
  have leftBound : (Word.mk (w 20).val (w 21).val).Bounded := by
    have bound := facts.readBounds importedConstraintsMemoryPorts[0]
      (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
          simp [importedConstraintsMemoryPorts])
    simpa [read_word, importedConstraintsMemoryPorts] using bound
  have result := rv_row_result hp arithmeticInverse core input.operation selected leftBound
  -- PC successor.
  have pcNext := pc_successor (by omega) arithmeticInverse core
    (initial := Word.ofBitVec entry.pc) (final := Word.mk (w 14).val (w 15).val)
    ⟨by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm,
     by rw [← pcWord]; exact (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩ (Word.ofBitVec_bound entry.pc)
  have finish : (⟨.mulDiv, w⟩ : Row p PooledFamily).finish.word.toBitVec = input.before.pc + 4 := by
    change (Word.mk (w 14).val (w 15).val).toBitVec = _
    rw [pcNext.2.2, Word.ofBitVec_roundtrip, facts.pc]
  have value : RV.alu input.operation.rvOp (input.before.getReg input.rs1) (input.before.getReg input.rs2) =
      memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) := by
    rw [left, right, leftWord, rightWord, outputWord, result]
  refine ⟨(input.before.setReg input.rd
      (RV.alu input.operation.rvOp (input.before.getReg input.rs1) (input.before.getReg input.rs2))).nextInstr,
    ?_, ?_⟩
  · cases hop : input.operation <;> simp [rvInstruction, hop, Operation.rvOp, RV.exec]
  · rw [value]
    exact rv_register_next written finish

end Airbender.Trace.Proofs
