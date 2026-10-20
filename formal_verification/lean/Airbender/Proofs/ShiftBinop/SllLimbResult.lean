import Airbender.Proofs.ShiftBinop.LimbModel
import Airbender.Review.Circuits.ShiftBinop.ResultsModel

namespace Airbender.ShiftBinop.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The native two-limb SLL pieces reconstruct the whole RV32 shift. -/
theorem sll_limb_result (lo hi : Nat) (amount : Fin 32)
    (_low : lo < 65536) (_high : hi < 65536) :
    (limbPieces .sll lo hi amount.val)[0] +
      (limbPieces .sll lo hi amount.val)[1] +
      (limbPieces .sll lo hi amount.val)[2] =
      ShiftKind.result .sll (Word.toBitVec ⟨lo,hi⟩) amount.val := by
  apply BitVec.eq_of_toNat_eq
  have zeroBits : (0 : BitVec 32).toNat = 0 := rfl
  fin_cases amount <;>
    norm_num [limbPieces,ShiftKind.result,Word.toBitVec,Word.value,limbBase,
      BitVec.toNat_zero,BitVec.toNat_add,BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow,Nat.add_mul,Nat.mul_add] <;>
    (try simp only [zeroBits]) <;> omega

end Airbender.ShiftBinop.Proofs
