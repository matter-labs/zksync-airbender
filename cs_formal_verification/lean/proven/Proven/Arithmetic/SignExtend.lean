module
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Airbender.Arithmetic

/-- `signExtend 32` of a 12-bit immediate fills both upper bytes from the second byte's sign bit. -/
theorem sign_extend_high_bytes (imm : BitVec 12) (i : Fin 2) :
    ((imm.signExtend 32).extractLsb' (16 + 8 * i.val) 8).toNat =
      if ((imm.signExtend 32).extractLsb' 8 8).toNat < 128 then 0 else 255 := by
  have sign : ((imm.signExtend 32).extractLsb' 8 8).msb = imm.msb := by
    simp only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb', BitVec.getLsbD_signExtend]
    norm_num
  have threshold : ((imm.signExtend 32).extractLsb' 8 8).toNat < 128 ↔ imm.msb = false := by
    rw [← sign, BitVec.msb_eq_false_iff_two_mul_lt]
    norm_num
    omega
  have bytes : (imm.signExtend 32).extractLsb' (16 + 8 * i.val) 8 =
      if imm.msb then 255#8 else 0#8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have within : 16 + 8 * i.val + k < 32 := by have := i.isLt; omega
    have high : ¬ 16 + 8 * i.val + k < 12 := by omega
    cases hsign : imm.msb <;>
      simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
        BitVec.getLsbD_signExtend, within, high, ite_false, hsign]
    all_goals interval_cases k <;> decide
  rw [bytes]
  cases hsign : imm.msb
  · have small := threshold.mpr hsign
    simp only [Bool.false_eq_true, ite_false, ite_eq_left small, BitVec.toNat_ofNat]
  · have large : ¬ ((imm.signExtend 32).extractLsb' 8 8).toNat < 128 := by
      intro small
      have impossible := (threshold.mp small).symm.trans hsign
      cases impossible
    simp only [ite_true, ite_eq_right large, BitVec.toNat_ofNat]

end Airbender.Arithmetic
