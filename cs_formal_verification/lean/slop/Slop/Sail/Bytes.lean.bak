import SailRV32
import Mathlib.Tactic.IntervalCases
import Slop.Arithmetic.Bytes
namespace Airbender.Reference.Sail

/-- The original Sail RV32 sign extension fills both upper bytes from the
    second byte's sign bit. Used to interpret native immediate metadata. -/
theorem sign_extend_high_bytes (imm : BitVec 12) (i : Fin 2) :
    ((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' (16 + 8 * i.val) 8).toNat =
      if ((SailRV32.Functions.sign_extend (m := 32) imm).extractLsb' 8 8).toNat < 128 then 0 else 255 := by
  change ((imm.signExtend 32).extractLsb' (16 + 8 * i.val) 8).toNat =
    if ((imm.signExtend 32).extractLsb' 8 8).toNat < 128 then 0 else 255
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

set_option maxRecDepth 4096 in
/-- The original Sail byte loop, specialized to RV32. -/
theorem rev8_bytes (x : BitVec 32) : SailRV32.Functions.rev8 x =
    ((x.extractLsb' 0 8) ++ (x.extractLsb' 8 8)) ++
      ((x.extractLsb' 16 8) ++ (x.extractLsb' 24 8)) := by
  simp [SailRV32.Functions.rev8, SailRV32.Functions.zeros,
    ForIn.forIn, ForIn'.forIn', IntRange.forIn', IntRange.forIn'.loop,
    Membership.mem, Sail.BitVec.length]

  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_append
    (x := (x.extractLsb' 0 8) ++ (x.extractLsb' 8 8))
    (y := (x.extractLsb' 16 8) ++ (x.extractLsb' 24 8)),
    BitVec.getLsbD_append (x := x.extractLsb' 16 8) (y := x.extractLsb' 24 8),
    BitVec.getLsbD_append (x := x.extractLsb' 0 8) (y := x.extractLsb' 8 8)]
  interval_cases k <;> simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange',
      Sail.BitVec.extractLsb, BitVec.extractLsb]

/-- Numerical form used to assemble the circuit's four byte contributions. -/
theorem rev8_value (x : BitVec 32) :
    (SailRV32.Functions.rev8 x).toNat =
      16777216 * (x.extractLsb' 0 8).toNat + 65536 * (x.extractLsb' 8 8).toNat +
      256 * (x.extractLsb' 16 8).toNat + (x.extractLsb' 24 8).toNat := by
  have append_value {m n : Nat} (a : BitVec m) (b : BitVec n) :
      (a ++ b).toNat = a.toNat * 2 ^ n + b.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  rw [rev8_bytes, append_value, append_value, append_value]
  norm_num
  ring

end Airbender.Reference.Sail
