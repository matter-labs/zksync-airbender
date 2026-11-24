module
public import Human.Circuits.JumpBranchSlt.RVModel
public import Proven.Arithmetic.Word

@[expose] public section

/-! Native decoder metadata of the RV comparison, branch and jump rows' instructions: `rvPooledDecoderFields` of
    `rvInstruction input` is the JumpBranchSlt projection (`JumpBranchSlt.rvDecoderFields`), a function of the
    instruction datatype. Also: `RV.decode` gives even JAL and branch offsets (their encodings end in a zero bit). -/

namespace Airbender.JumpBranchSlt.Proofs
open Arithmetic Trace

/-- The decoder data of `Comparison.rvInstruction input` (`rd ≠ 0`; writes to x0 are not in this family's table). -/
def comparisonData (input : Comparison.RVInput) : DecoderData Unit :=
  match input.opcode with
  | .slt => ⟨(), input.rs1, input.rs2, input.rd, ⟨0, 0⟩, 4, 2⟩
  | .slti => ⟨(), input.rs1, 0, input.rd, Word.ofBitVec (input.encodedImmediate.signExtend 32), 4, 2⟩
  | .sltu => ⟨(), input.rs1, input.rs2, input.rd, ⟨0, 0⟩, 4, 3⟩
  | .sltiu => ⟨(), input.rs1, 0, input.rd, Word.ofBitVec (input.encodedImmediate.signExtend 32), 4, 3⟩

/-- The decoder data of `Branch.rvInstruction input`. -/
def branchData (input : Branch.RVInput) : DecoderData Unit :=
  ⟨(), input.rs1, input.rs2, 0, Word.ofBitVec (input.encodedOffset.signExtend 32), 24, Branch.rvFunct3 input.cond⟩

/-- The decoder data of `Jump.rvInstruction input`. -/
def jumpData (input : Jump.RVInput) : DecoderData Unit :=
  match input.instruction with
  | .jal offset => ⟨(), 0, 0, input.rd, Word.ofBitVec (offset.signExtend 32), if input.rd = 0 then 17 else 1, 0⟩
  | .jalr offset =>
    ⟨(), input.rs1, 0, input.rd, Word.ofBitVec (offset.signExtend 32), if input.rd = 0 then 18 else 2, 0⟩

theorem comparison_pooled_fields {input : Comparison.RVInput} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields (Comparison.rvInstruction input) = some data) (family : data.family = .jumpBranchSlt) :
    data = (comparisonData input).mapFamily (fun _ => .jumpBranchSlt) := by
  obtain ⟨opcode, _, _, _, rs1, rs2, rd, imm, _⟩ := input
  by_cases zero : rd = 0
  · subst zero
    cases opcode <;> simp [rvPooledDecoderFields, Comparison.rvInstruction, Trace.rvDecoderFields] at fields <;>
      (subst fields; simp [DecoderData.mapFamily, pooledArithmeticFamily, arithmeticFields] at family)
  · have nz : rd ≠ 0#5 := zero
    cases opcode <;> simp [rvPooledDecoderFields, Comparison.rvInstruction, Trace.rvDecoderFields,
      JumpBranchSlt.rvDecoderFields, nz] at fields <;> (subst fields; rfl)

theorem branch_pooled_fields {input : Branch.RVInput} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields (Branch.rvInstruction input) = some data) (_family : data.family = .jumpBranchSlt) :
    data = (branchData input).mapFamily (fun _ => .jumpBranchSlt) := by
  simp [rvPooledDecoderFields, Branch.rvInstruction, Trace.rvDecoderFields,
    JumpBranchSlt.rvDecoderFields] at fields
  simp [← fields, branchData, DecoderData.mapFamily]

theorem jump_pooled_fields {input : Jump.RVInput} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields (Jump.rvInstruction input) = some data) (_family : data.family = .jumpBranchSlt) :
    data = (jumpData input).mapFamily (fun _ => .jumpBranchSlt) := by
  obtain ⟨instruction, _, _, _, rs1, rd, _⟩ := input
  cases instruction <;> simp [rvPooledDecoderFields, Jump.rvInstruction, Trace.rvDecoderFields,
      JumpBranchSlt.rvDecoderFields] at fields <;>
    simp [← fields, jumpData, DecoderData.mapFamily]

private theorem low_bit_even {n : Nat} (x : BitVec n) :
    ((x ++ (0 : BitVec 1)).signExtend 32).toNat % 2 = 0 := by
  have bit : ((x ++ (0 : BitVec 1)).signExtend 32)[0] = false := by
    rw [BitVec.getElem_signExtend]
    simp [BitVec.getElem_append]
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD, Nat.testBit_zero] at bit
  simpa using bit

/-- `RV.decode` gives a JAL an even offset. -/
theorem decode_jal_even {bits : RV.Word} {rd : RV.Reg} {offset : RV.Word}
    (h : RV.decode bits = some (.jal rd offset)) : offset.toNat % 2 = 0 := by
  unfold RV.decode at h
  simp only at h
  split at h
  all_goals (try simp only [RV.decodeCsr, RV.decodeMopR] at h)
  all_goals (try split_ifs at h)
  all_goals try first
    | (cases h; done)
    | (obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp h; cases h; done)
  all_goals obtain ⟨rfl, rfl⟩ := RV.Instr.jal.inj (Option.some.inj h)
  exact low_bit_even _

/-- `RV.decode` gives a branch an even offset. -/
theorem decode_branch_even {bits : RV.Word} {cond : RV.Cond} {rs1 rs2 : RV.Reg} {offset : RV.Word}
    (h : RV.decode bits = some (.branch cond rs1 rs2 offset)) : offset.toNat % 2 = 0 := by
  unfold RV.decode at h
  simp only at h
  split at h
  all_goals (try simp only [RV.decodeCsr, RV.decodeMopR] at h)
  all_goals (try split_ifs at h)
  all_goals try first
    | (cases h; done)
    | (obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp h; cases h; done)
  all_goals obtain ⟨rfl, rfl, rfl, rfl⟩ := RV.Instr.branch.inj (Option.some.inj h)
  all_goals exact low_bit_even _

end Airbender.JumpBranchSlt.Proofs
