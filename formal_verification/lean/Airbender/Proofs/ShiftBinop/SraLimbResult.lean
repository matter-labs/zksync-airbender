import Airbender.Proofs.ShiftBinop.LimbModel
import Airbender.Review.Circuits.ShiftBinop.ResultsModel

namespace Airbender.ShiftBinop.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem limb_word_msb (lo hi : Nat) (_low : lo < 65536) (_high : hi < 65536) :
    (Word.toBitVec ⟨lo,hi⟩).msb = decide (32768 ≤ hi) := by
  rw [BitVec.msb_eq_decide]
  congr 1
  change (2147483648 ≤ (lo + 65536 * hi) % 4294967296) = (32768 ≤ hi)
  have small : lo + 65536 * hi < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt small]
  apply propext
  omega

/-- The positive sign domain is checked separately within the default budget. -/
theorem sra_positive_limb_result (lo hi : Nat) (amount : Fin 32)
    (low : lo < 65536) (high : hi < 65536) (sign : hi < 32768) :
    (limbPieces .sra lo hi amount.val)[0] +
      (limbPieces .sra lo hi amount.val)[1] +
      (limbPieces .sra lo hi amount.val)[2] =
      ShiftKind.result .sra (Word.toBitVec ⟨lo,hi⟩) amount.val := by
  apply BitVec.eq_of_toNat_eq
  have zeroBits : (0 : BitVec 32).toNat = 0 := rfl
  have msb : (Word.toBitVec ⟨lo,hi⟩).msb = false := by
    rw [limb_word_msb lo hi low high]
    simp only [show ¬32768 ≤ hi by omega,decide_false]
  rw [ShiftKind.result,BitVec.toNat_sshiftRight_of_msb_false msb]
  fin_cases amount <;>
    norm_num [limbPieces,Word.toBitVec,Word.value,limbBase,
      BitVec.toNat_zero,BitVec.toNat_add,BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow,Nat.add_mul,Nat.mul_add,sign] <;>
    (try simp only [zeroBits]) <;> omega

/-- The negative sign domain is checked separately within the default budget. -/
theorem sra_negative_limb_result (lo hi : Nat) (amount : Fin 32)
    (low : lo < 65536) (high : hi < 65536) (sign : ¬hi < 32768) :
    (limbPieces .sra lo hi amount.val)[0] +
      (limbPieces .sra lo hi amount.val)[1] +
      (limbPieces .sra lo hi amount.val)[2] =
      ShiftKind.result .sra (Word.toBitVec ⟨lo,hi⟩) amount.val := by
  apply BitVec.eq_of_toNat_eq
  have msb : (Word.toBitVec ⟨lo,hi⟩).msb = true := by
    rw [limb_word_msb lo hi low high]
    simp only [show 32768 ≤ hi by omega,decide_true]
  rw [ShiftKind.result,BitVec.toNat_sshiftRight_of_msb_true msb]
  fin_cases amount <;>
    norm_num [limbPieces,Word.toBitVec,Word.value,limbBase,
      BitVec.toNat_zero,BitVec.toNat_add,BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow,Nat.add_mul,Nat.mul_add,sign] <;>
    omega

/-- Native sign fill and both logical pieces reconstruct every whole RV32 SRA. -/
theorem sra_limb_result (lo hi : Nat) (amount : Fin 32)
    (low : lo < 65536) (high : hi < 65536) :
    (limbPieces .sra lo hi amount.val)[0] +
      (limbPieces .sra lo hi amount.val)[1] +
      (limbPieces .sra lo hi amount.val)[2] =
      ShiftKind.result .sra (Word.toBitVec ⟨lo,hi⟩) amount.val := by
  by_cases sign : hi < 32768
  · exact sra_positive_limb_result lo hi amount low high sign
  · exact sra_negative_limb_result lo hi amount low high sign

end Airbender.ShiftBinop.Proofs
