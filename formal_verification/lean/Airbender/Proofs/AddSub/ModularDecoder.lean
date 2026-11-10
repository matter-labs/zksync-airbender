import Airbender.Review.Helpers.Decoder.ModularProgram
import Airbender.Proofs.Trace.PooledProgram

namespace Airbender.AddSub.Modular.Proofs
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

theorem mop_sound {mop : BitVec 3} {opcode : Opcode}
    (selected : opcodeOfMop mop = some opcode) : mop = opcode.mop := by
  unfold opcodeOfMop at selected
  split_ifs at selected <;> cases selected <;> assumption

theorem standard_fields {original : SailRV32.instruction} {data : DecoderData}
    (fields : Trace.decoderFields original = some data) :
    Modular.decoderFields original = some data := by
  unfold Modular.decoderFields
  split
  · simp [Trace.decoderFields] at fields
  · exact fields

theorem fields_cases {original : SailRV32.instruction} {data : DecoderData}
    (fields : Modular.decoderFields original = some data) :
    Trace.decoderFields original = some data ∨
      ∃ opcode rs1 rs2 rd, original = instruction opcode rs1 rs2 rd ∧
        data = nativeData opcode rs1 rs2 rd := by
  unfold Modular.decoderFields at fields
  split at fields
  · rename_i mop rs2 rs1 rd
    cases selected : opcodeOfMop mop with
    | none => simp [selected] at fields
    | some opcode =>
      have dataEq : data = nativeData opcode rs1 rs2 rd := by
        simpa [selected] using fields.symm
      exact Or.inr ⟨opcode, rs1, rs2, rd, by rw [mop_sound selected]; rfl, dataEq⟩
  · exact Or.inl fields

theorem field_bounds {original : SailRV32.instruction} {data : DecoderData}
    (fields : Modular.decoderFields original = some data) :
    data.immediate.Bounded ∧ data.mask < 512 := by
  rcases fields_cases fields with standard | ⟨opcode, rs1, rs2, rd, _, rfl⟩
  · have bounds := decoder_field_bounds standard
    exact ⟨bounds.1, by omega⟩
  · unfold nativeData arithmeticFields
    split
    · exact ⟨by constructor <;> decide, by decide⟩
    · exact ⟨Word.ofBitVec_bound 0, by change 2 ^ (opcode.selector - 10) < 512; cases opcode <;> decide⟩

theorem native_family (opcode : Opcode) (rs1 rs2 rd : BitVec 5) :
    (nativeData opcode rs1 rs2 rd).family = .addSub := by
  unfold nativeData arithmeticFields
  split <;> rfl

theorem native_rd (opcode : Opcode) (rs1 rs2 rd : BitVec 5) :
    (nativeData opcode rs1 rs2 rd).rd = rd := by
  unfold nativeData arithmeticFields
  split
  · exact (by assumption : rd = 0).symm
  · rfl

theorem memory_fields {original : SailRV32.instruction} {data : DecoderData}
    (fields : Modular.decoderFields original = some data) (family : data.family = .wordMemory) :
    Trace.decoderFields original = some data := by
  rcases fields_cases fields with standard | ⟨opcode, rs1, rs2, rd, _, rfl⟩
  · exact standard
  · rw [native_family] at family
    cases family

def decoderRules : DecoderRules Modular.decoderFields where
  bounds _ _ := field_bounds
  zeroNop _ _ fields family zero := by
    rcases fields_cases fields with standard | ⟨opcode, rs1, rs2, rd, _, rfl⟩
    · exact decoder_zero_nop standard family zero
    · rw [native_rd] at zero
      subst rd
      rfl
  loadNonzero _ _ fields family load := decoder_load_nonzero (memory_fields fields family) family load

end Airbender.AddSub.Modular.Proofs
