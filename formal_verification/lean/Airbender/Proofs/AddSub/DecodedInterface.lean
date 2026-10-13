import Airbender.Proofs.AddSub.RowModel
import Airbender.Review.Helpers.Program
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.AddSub.Proofs
open Arithmetic Trace Reference.RiscV Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

def arithmeticData (input : Input) : DecoderData :=
  match input.rs1, input.rs2, input.rd with
  | .Regidx rs1, .Regidx rs2, .Regidx rd => match input.row.opcode with
    | .add => arithmeticFields rs1 rs2 rd 0 1
    | .addi => arithmeticFields rs1 0 rd (SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate) 1
    | .sub => arithmeticFields rs1 rs2 rd 0 2
    | .lui => arithmeticFields 0 0 rd (input.encodedUpperImmediate ++ BitVec.ofNat 12 0) 1
    | .auipc => arithmeticFields 0 0 rd (input.encodedUpperImmediate ++ BitVec.ofNat 12 0) 4

theorem reference_interface (input : Input)
    (leftBound : input.row.left.Bounded) (rightBound : input.row.right.Bounded)
    (immediate : input.row.immediate = (arithmeticData input).immediate)
    (left : run (SailRV32.Functions.rX_bits (.Regidx (arithmeticData input).rs1)) input.before =
      .ok input.row.left.toBitVec input.before)
    (right : run (SailRV32.Functions.rX_bits (.Regidx (arithmeticData input).rs2)) input.before =
      .ok input.row.right.toBitVec input.before)
    (originalLeft : ∃ value, run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok value input.before)
    (originalRight : ∃ value, run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok value input.before)
    (pc : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.row.pc.toBitVec input.before) :
    Preprocessing input ∧ Contract input := by
  rcases input with ⟨⟨opcode, leftWord, rightWord, immediateWord, pcWord⟩,
    ⟨rs1⟩, ⟨rs2⟩, ⟨rd⟩, encodedImmediate, encodedUpper, before⟩
  change BitVec 5 at rs1 rs2 rd
  have zeroLeft (zero : (arithmeticData
      ⟨⟨opcode, leftWord, rightWord, immediateWord, pcWord⟩,
        .Regidx rs1, .Regidx rs2, .Regidx rd, encodedImmediate, encodedUpper, before⟩).rs1 = 0) :
      leftWord = ⟨0, 0⟩ := by
    rw [zero] at left
    change EStateM.Result.ok (0 : BitVec 32) before = .ok leftWord.toBitVec before at left
    exact Word.eq_zero_of_bounded leftBound (EStateM.Result.ok.inj left).1.symm
  have zeroRight (zero : (arithmeticData
      ⟨⟨opcode, leftWord, rightWord, immediateWord, pcWord⟩,
        .Regidx rs1, .Regidx rs2, .Regidx rd, encodedImmediate, encodedUpper, before⟩).rs2 = 0) :
      rightWord = ⟨0, 0⟩ := by
    rw [zero] at right
    change EStateM.Result.ok (0 : BitVec 32) before = .ok rightWord.toBitVec before at right
    exact Word.eq_zero_of_bounded rightBound (EStateM.Result.ok.inj right).1.symm
  constructor
  · by_cases zero : rd = (0#5)
    · have l := zeroLeft (by cases opcode <;> simp [arithmeticData, arithmeticFields, zero])
      have r := zeroRight (by cases opcode <;> simp [arithmeticData, arithmeticFields, zero])
      have i : immediateWord = ⟨0, 0⟩ := by
        cases opcode <;> simpa [arithmeticData, arithmeticFields, zero] using immediate
      simpa [Preprocessing, zero, zeroRegister] using And.intro l (And.intro r i)
    · have nonzero : (.Regidx rd : SailRV32.regidx) ≠ zeroRegister := by
        simpa [zeroRegister] using zero
      dsimp only [Preprocessing]
      rw [if_neg nonzero]
      cases opcode
      · simpa [arithmeticData, arithmeticFields, zero, Word.ofBitVec] using immediate
      · exact zeroRight (by simp [arithmeticData, arithmeticFields, zero])
      · simpa [arithmeticData, arithmeticFields, zero, Word.ofBitVec] using immediate
      · exact ⟨zeroLeft (by simp [arithmeticData, arithmeticFields, zero]),
          zeroRight (by simp [arithmeticData, arithmeticFields, zero])⟩
      · exact ⟨zeroLeft (by simp [arithmeticData, arithmeticFields, zero]),
          zeroRight (by simp [arithmeticData, arithmeticFields, zero])⟩
  · constructor
    · intro used
      by_cases zero : rd = (0#5)
      · obtain ⟨value, read⟩ := originalLeft
        exact ⟨value, read, by simp [zeroRegister, zero]⟩
      · cases opcode <;> simp only at used
        all_goals first
          | (solve | simp at used)
          | (exact ⟨_, by simpa [arithmeticData, arithmeticFields, zero] using left, fun _ => rfl⟩)
    · intro used
      by_cases zero : rd = (0#5)
      · obtain ⟨value, read⟩ := originalRight
        exact ⟨value, read, by simp [zeroRegister, zero]⟩
      · cases opcode <;> simp only at used
        all_goals first
          | (solve | simp at used)
          | (exact ⟨_, by simpa [arithmeticData, arithmeticFields, zero] using right, fun _ => rfl⟩)
    · intro nonzero used
      have zero : rd ≠ (0#5) := by simpa [zeroRegister] using nonzero
      change opcode = .addi at used
      subst opcode
      simpa [arithmeticData, arithmeticFields, zero, Word.ofBitVec_roundtrip] using
        congrArg Word.toBitVec immediate
    · intro nonzero used
      have zero : rd ≠ (0#5) := by simpa [zeroRegister] using nonzero
      change opcode = .lui ∨ opcode = .auipc at used
      rcases used with rfl | rfl
      all_goals simpa [arithmeticData, arithmeticFields, zero, Word.ofBitVec_roundtrip,
        SailRV32.Functions.sign_extend, Sail.BitVec.signExtend] using congrArg Word.toBitVec immediate
    · exact pc

end Airbender.AddSub.Proofs
