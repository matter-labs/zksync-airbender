import Airbender.Review.Circuits.ShiftBinop.ShiftModel
import Airbender.Review.Circuits.ShiftBinop.Lookups
import Airbender.Review.Helpers.Tables.NativeShiftScalars
import Airbender.Review.Helpers.Tables.NativeSllLow
import Airbender.Review.Helpers.Tables.NativeSllHigh
import Airbender.Review.Helpers.Tables.NativeSrlLow
import Airbender.Review.Helpers.Tables.NativeSrlHigh

namespace Airbender.ShiftBinop.Proofs
open Arithmetic Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Resolve an actual combined-table contribution into its exact canonical
    native key, both limb bounds and RV32 contribution. -/
theorem native_part_result (part : ShiftPart) (query : Vector (ZMod mersenne31Modulus) 3)
    (member : (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[]
      (query.push (part.tag : ZMod mersenne31Modulus))) :
    query[0].val < 2097152 ∧ (Word.mk query[1].val query[2].val).Bounded ∧
      (Word.mk query[1].val query[2].val).toBitVec = part.result query[0].val := by
  cases part
  · obtain ⟨key,lo,hi,result⟩ := native_sll_low_result query ((native_lookup_sll_low query).mp member)
    exact ⟨key,⟨lo,hi⟩,by simpa [Word.toBitVec,Word.value,limbBase,ShiftPart.result,Nat.mul_comm] using result⟩
  · obtain ⟨key,hi,zero,result⟩ := native_sll_high_result query ((native_lookup_sll_high query).mp member)
    exact ⟨key,⟨by simp [zero,limbBase],hi⟩,
      by simpa [Word.toBitVec,Word.value,limbBase,ShiftPart.result,zero,Nat.mul_comm] using result⟩
  · obtain ⟨key,lo,zero,result⟩ := native_srl_low_result query ((native_lookup_srl_low query).mp member)
    exact ⟨key,⟨lo,by simp [zero,limbBase]⟩,
      by simpa [Word.toBitVec,Word.value,limbBase,ShiftPart.result,zero,Nat.mul_comm] using result⟩
  · obtain ⟨key,lo,hi,result⟩ := native_srl_high_result query ((native_lookup_srl_high query).mp member)
    exact ⟨key,⟨lo,hi⟩,by simpa [Word.toBitVec,Word.value,limbBase,ShiftPart.result,Nat.mul_comm] using result⟩
  · obtain ⟨key,lo,hi,result⟩ := native_shift_sign_fill query ((native_lookup_scalar .signFill query).mp member)
    exact ⟨key,⟨lo,hi⟩,by simpa [Word.toBitVec,Word.value,limbBase,ShiftPart.result,Nat.mul_comm] using result⟩
  · have zero := (native_lookup_zero query).mp member
    subst query
    norm_num [Word.Bounded,Word.toBitVec,Word.value,limbBase,ShiftPart.result]
    rfl

end Airbender.ShiftBinop.Proofs
