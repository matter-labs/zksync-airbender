import Slop.Trace.RVPooledStep
import Slop.Trace.RVPooledRow
import Slop.JumpBranchSlt.RVTraceSoundness
import Slop.ISA.RV.DecodeShape

/-! One comparison/branch/jump row of a pooled trace is one `RV.exec` of its instruction (`RVPooledRowStep`), from
    the row's own RV history: the row facts of `JumpBranchSlt.Proofs.rv_row_facts` (`RVRowFacts`) with the operand
    reads taken from the history, then `rv_comparison_exec` / `rv_branch_exec` / `rv_jump_exec`. A branch writes x0. -/

namespace Airbender.Trace.Proofs
open Arithmetic JumpBranchSlt JumpBranchSlt.Proofs

/-- The row facts and the history's destination write, for any family data `data` of the entry. -/
theorem rv_jbs_facts {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p) {trace : PooledTrace p} {initial : RV.State}
    {cells : List Cell} {w : Nat → ZMod p} {before after : RV.State} {entry : RVPooledProgramEntry}
    (facts : RVPooledRowFacts trace initial cells ⟨.jumpBranchSlt, w⟩ before after entry)
    {data : DecoderData Unit} (dataEq : entry.data = data.mapFamily (fun _ => .jumpBranchSlt))
    (small : data.mask < 32) :
    RVRowFacts w before data ∧ RV.Same after (before.setReg data.rd (Word.mk (w 30).val (w 31).val).toBitVec) := by
  have h := Verification.holds_of_sublist facts.constraints
    (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  have beforePC := facts.pc
  have aligned := facts.pcAligned
  have readBounds := facts.readBounds
  have finish := facts.finishBound
  have history := facts.history
  have query := facts.query
  obtain ⟨pc, entryBits, entryData⟩ := entry
  change entryData = data.mapFamily (fun _ => .jumpBranchSlt) at dataEq
  subst dataEq
  have query0 : decoderQuery w = (⟨pc, entryBits, data⟩ : JumpBranchSlt.RVProgramEntry).query := query
  change before.pc = pc at beforePC
  change pc.toNat % 4 = 0 at aligned
  have pcWord := rv_native_query_pc_word limbSize query0
  change Word.mk (w 0).val (w 1).val = Word.ofBitVec pc at pcWord
  rw [← beforePC] at pcWord aligned
  have rs1Query := congrArg (fun q : Vector (ZMod p) 9 => q[2]) query0
  change w 5 = (data.rs1.toNat : ZMod p) at rs1Query
  have rs2Query := congrArg (fun q : Vector (ZMod p) 9 => q[3]) query0
  change w 6 = (data.rs2.toNat : ZMod p) at rs2Query
  have rdQuery := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query0
  change w 7 = (data.rd.toNat : ZMod p) at rdQuery
  have shape : (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).ports =
      #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[1],
        importedConstraintsMemoryPorts[2]] := by
    have portsEq : (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).ports = importedConstraintsMemoryPorts := rfl
    rw [portsEq]
    rfl
  dsimp only [rowEvents] at history
  rw [shape] at history
  obtain ⟨left, right, written⟩ := rv_register_row (by omega) trace.memoryEpoch
    (by simp [importedConstraintsMemoryPorts]) (by simp [importedConstraintsMemoryPorts])
    rfl rfl rfl rs1Query rs2Query rdQuery history
  have leftWord : memoryWord ((importedConstraintsMemoryPorts[0]).readCode w) =
      (Word.mk (w 22).val (w 23).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have rightWord : memoryWord ((importedConstraintsMemoryPorts[1]).readCode w) =
      (Word.mk (w 26).val (w 27).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.readCode, pairCode, memoryWord]
  have outputWord : memoryWord ((importedConstraintsMemoryPorts[2]).writeCode w) =
      (Word.mk (w 30).val (w 31).val).toBitVec := by
    simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord]
  have leftBound := readBounds importedConstraintsMemoryPorts[0]
    (by change importedConstraintsMemoryPorts[0] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have rightBound := readBounds importedConstraintsMemoryPorts[1]
    (by change importedConstraintsMemoryPorts[1] ∈ importedConstraintsMemoryPorts
        simp [importedConstraintsMemoryPorts])
  have bounds : (Word.mk (w 22).val (w 23).val).Bounded ∧
      (Word.mk (w 26).val (w 27).val).Bounded := by
    simpa [read_word, importedConstraintsMemoryPorts] using And.intro leftBound rightBound
  change (Word.mk (w 16).val (w 17).val).Bounded at finish
  have flags := rv_decoder_selectors limbSize h small query0
  have low := congrArg (fun q : Vector (ZMod p) 9 => q[5]) query0
  change w 8 = (data.immediate.lo : ZMod p) at low
  have high := congrArg (fun q : Vector (ZMod p) 9 => q[6]) query0
  change w 9 = (data.immediate.hi : ZMod p) at high
  have tag := congrArg (fun q : Vector (ZMod p) 9 => q[7]) query0
  change w 10 = (data.funct3 : ZMod p) at tag
  refine ⟨⟨h, pcWord, aligned, low, high, tag, ?_, left.trans leftWord, right.trans rightWord, bounds.1, bounds.2,
    finish.2⟩, outputWord ▸ written⟩
  intro k
  have flag := flags k
  fin_cases k <;> simpa [importedConstraintsDecoderColumns] using flag

theorem rv_comparison_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {after : RV.State} {entry : RVPooledProgramEntry} (input : Comparison.RVInput)
    (facts : RVPooledRowFacts trace initial cells ⟨.jumpBranchSlt, w⟩ input.before after entry)
    (fields : rvPooledDecoderFields (Comparison.rvInstruction input) = some entry.data) :
    RVPooledRowStep ⟨.jumpBranchSlt, w⟩ input.before after (Comparison.rvInstruction input) := by
  obtain ⟨rowFacts, written⟩ := rv_jbs_facts hp facts (comparison_pooled_fields fields facts.family)
    (by unfold comparisonData; split <;> simp)
  have rd : (comparisonData input).rd = input.rd := by unfold comparisonData; split <;> rfl
  rw [rd] at written
  obtain ⟨s', exec, same⟩ := rv_comparison_exec (by omega) rowFacts
    (output := ⟨⟨(w 30).val, (w 31).val⟩, ⟨(w 16).val, (w 17).val⟩⟩) rfl rfl rfl rfl
  exact ⟨s', exec, same.trans (rv_same_with_pc written _)⟩

theorem rv_branch_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {after : RV.State} {entry : RVPooledProgramEntry} (input : Branch.RVInput)
    (facts : RVPooledRowFacts trace initial cells ⟨.jumpBranchSlt, w⟩ input.before after entry)
    (fields : rvPooledDecoderFields (Branch.rvInstruction input) = some entry.data)
    (decodes : RV.decode entry.bits = some (Branch.rvInstruction input)) :
    RVPooledRowStep ⟨.jumpBranchSlt, w⟩ input.before after (Branch.rvInstruction input) := by
  obtain ⟨rowFacts, written⟩ := rv_jbs_facts hp facts (branch_pooled_fields fields facts.family)
    (by simp [branchData])
  obtain ⟨s', exec, same⟩ := rv_branch_exec (by omega) rowFacts (decode_branch_even decodes)
    (output := ⟨⟨(w 30).val, (w 31).val⟩, ⟨(w 16).val, (w 17).val⟩⟩) rfl rfl
  exact ⟨s', exec, same.trans (rv_same_with_pc (written.trans (rv_same_set_zero _ _)) _)⟩

theorem rv_jump_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {after : RV.State} {entry : RVPooledProgramEntry} (input : Jump.RVInput)
    (facts : RVPooledRowFacts trace initial cells ⟨.jumpBranchSlt, w⟩ input.before after entry)
    (fields : rvPooledDecoderFields (Jump.rvInstruction input) = some entry.data)
    (decodes : RV.decode entry.bits = some (Jump.rvInstruction input)) :
    RVPooledRowStep ⟨.jumpBranchSlt, w⟩ input.before after (Jump.rvInstruction input) := by
  obtain ⟨rowFacts, written⟩ := rv_jbs_facts hp facts (jump_pooled_fields fields facts.family)
    (by unfold jumpData; split <;> split <;> simp)
  have rd : (jumpData input).rd = input.rd := by unfold jumpData; split <;> rfl
  rw [rd] at written
  have even : ∀ offset, input.instruction = .jal offset → (offset.signExtend 32).toNat % 2 = 0 := by
    intro offset jal
    have d := decodes
    simp only [Jump.rvInstruction, jal] at d
    exact decode_jal_even d
  obtain ⟨s', exec, same⟩ := rv_jump_exec (by omega) rowFacts even
    (output := ⟨⟨(w 30).val, (w 31).val⟩, ⟨(w 16).val, (w 17).val⟩⟩) rfl rfl rfl rfl
  exact ⟨s', exec, same.trans (rv_same_with_pc written _)⟩

theorem rv_jbs_row_step {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {w : Nat → ZMod p} {before after : RV.State} {entry : RVPooledProgramEntry} {i : RV.Instr}
    (facts : RVPooledRowFacts trace initial cells ⟨.jumpBranchSlt, w⟩ before after entry)
    (fields : rvPooledDecoderFields i = some entry.data) (decodes : RV.decode entry.bits = some i) :
    RVPooledRowStep ⟨.jumpBranchSlt, w⟩ before after i := by
  obtain ⟨d, fd, _⟩ := (rv_pooled_fields_family fields).2.1 facts.family
  have shape := RV.decode_shape decodes
  cases i with
  | op op rd rs1 rs2 =>
    cases op <;> simp only [JumpBranchSlt.rvDecoderFields, reduceCtorEq] at fd
    · exact rv_comparison_step hp ⟨.slt, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, 0, before⟩ facts fields
    · exact rv_comparison_step hp ⟨.sltu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, rd, 0, before⟩ facts fields
  | opImm op rd rs1 imm =>
    simp only [RV.Shape] at shape
    rcases shape with ⟨kind, x, rfl⟩ | ⟨kind, sh, rfl⟩
    · rcases kind with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [JumpBranchSlt.rvDecoderFields, reduceCtorEq] at fd
      · exact rv_comparison_step hp ⟨.slti, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, before⟩ facts fields
      · exact rv_comparison_step hp ⟨.sltiu, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, 0, rd, x, before⟩ facts fields
    · rcases kind with rfl | rfl | rfl <;> simp only [JumpBranchSlt.rvDecoderFields, reduceCtorEq] at fd
  | branch cond rs1 rs2 offset =>
    obtain ⟨x, rfl⟩ := shape
    exact rv_branch_step hp ⟨cond, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rs2, x, before⟩ facts fields decodes
  | jal rd offset =>
    obtain ⟨x, rfl⟩ := shape
    exact rv_jump_step hp ⟨.jal x, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, 0, rd, before⟩ facts fields decodes
  | jalr rd rs1 offset =>
    obtain ⟨x, rfl⟩ := shape
    exact rv_jump_step hp ⟨.jalr x, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, rs1, rd, before⟩ facts fields decodes
  | _ => simp [JumpBranchSlt.rvDecoderFields] at fd

end Airbender.Trace.Proofs
