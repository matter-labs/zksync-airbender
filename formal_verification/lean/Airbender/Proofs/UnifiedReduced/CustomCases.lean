import Airbender.Review.UnifiedReduced.CustomExecution
import Airbender.Proofs.UnifiedReduced.CustomDecoder

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem custom_instruction_cases {instruction : SailRV32.instruction}
    {data : Trace.DecoderData Trace.UnifiedFamily}
    (fields : customDecoderFields instruction = some data) :
    (∃ rs1 rs2 rd, instruction = .ZIMOP_MOP_RR (4, rs2, rs1, rd)) ∨
      ∃ rotation : Fin 4, ∃ rs1 rd, instruction =
        .ZIMOP_MOP_R (BitVec.ofNat 5 (XorRotate.amount rotation), rs1, rd) := by
  cases instruction with
  | ZIMOP_MOP_RR value =>
    rcases value with ⟨mop, rs2, rs1, rd⟩
    cases rs2; cases rs1; cases rd
    simp only [customDecoderFields] at fields
    split at fields
    · rename_i domain
      exact Or.inl ⟨_, _, _, by rw [domain.1]⟩
    · cases fields
  | ZIMOP_MOP_R value =>
    rcases value with ⟨mop, rs1, rd⟩
    rcases rs1 with ⟨rs1Bits⟩
    rcases rd with ⟨rdBits⟩
    simp only [customDecoderFields] at fields
    split at fields
    · cases fields
    · cases found : customRotationTag mop with
      | none => simp only [found, bind, Option.bind] at fields; cases fields
      | some tag =>
        unfold customRotationTag at found
        split_ifs at found with r16 r12 r8 r7
        · exact Or.inr ⟨0, .Regidx rs1Bits, .Regidx rdBits, by rw [r16]; rfl⟩
        · exact Or.inr ⟨1, .Regidx rs1Bits, .Regidx rdBits, by rw [r12]; rfl⟩
        · exact Or.inr ⟨2, .Regidx rs1Bits, .Regidx rdBits, by rw [r8]; rfl⟩
        · exact Or.inr ⟨3, .Regidx rs1Bits, .Regidx rdBits, by rw [r7]; rfl⟩
  | _ => cases fields

end Airbender.UnifiedReduced.Proofs
