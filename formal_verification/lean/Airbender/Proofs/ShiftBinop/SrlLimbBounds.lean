import Airbender.Proofs.ShiftBinop.LimbModel

namespace Airbender.ShiftBinop.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Native SRL contribution halves occupy disjoint bit positions. -/
theorem srl_limb_bounds (lo hi : Nat) (amount : Fin 32)
    (_low : lo < 65536) (_high : hi < 65536) :
    (piecesWord (limbPieces .srl lo hi amount.val)).Bounded := by
  have zeroBits : (0 : BitVec 32).toNat = 0 := rfl
  fin_cases amount <;>
    norm_num [piecesWord,limbPieces,Word.Bounded,Word.ofBitVec,limbBase,
      BitVec.toNat_zero,BitVec.toNat_shiftLeft,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,
      Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow] <;> simp only [zeroBits] <;> omega

end Airbender.ShiftBinop.Proofs
