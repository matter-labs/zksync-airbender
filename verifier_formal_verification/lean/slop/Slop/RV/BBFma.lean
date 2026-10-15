import Slop.RV.BBMont
import Slop.RV.Tactic
import Slop.RV.Code.bb_fma

/-! `bb_fma` (plain Rust, `fma_mod = add_mod(c, mul_mod(a, b))`). -/

namespace RV
open Spec
set_option maxHeartbeats 0

/-- `bb_fma`: `a1, a2 < p` ⇒ `a0 ← (a0 · a1 · 2^-32 + a2) mod p` (canonical). -/
def bbFmaPost : State → State → Prop := fun s s' =>
  (s.getReg 11#5).toNat < BabyBearP → (s.getReg 12#5).toNat < BabyBearP →
    (s'.getReg 10#5).toNat = ((s.getReg 10#5).toNat * (s.getReg 11#5).toNat * RINV + (s.getReg 12#5).toNat) % BabyBearP

theorem bb_fma_impl : Implements Code.bb_fma 16 bbFmaPost := by
  intro s hcall
  rv_start Code.bb_fma hcall
  rv_steps 29
  rv_ret
  refine ⟨by rv_regs, ?_, by rv_callee, by rv_frame⟩
  intro hb hc
  rv_regs
  generalize s.getReg 10#5 = A at *
  generalize s.getReg 11#5 = B at *
  generalize s.getReg 12#5 = C at *
  obtain ⟨hlt, heq⟩ := mont_reduce A.toNat B.toNat A.isLt hb
  have hlo : (B * A).toNat = A.toNat * B.toNat % 2 ^ 32 := by rw [BitVec.toNat_mul, Nat.mul_comm]
  have hm : (B * A * 2013265919#32).toNat = A.toNat * B.toNat % 2 ^ 32 * 0x77ffffff % 2 ^ 32 := by
    rw [BitVec.toNat_mul, hlo]; rfl
  generalize hX : BitVec.extractLsb' 32 32 (BitVec.zeroExtend 64 (B * A * 2013265919#32) *
    BitVec.zeroExtend 64 2013265921#32) = X
  generalize hY : BitVec.extractLsb' 32 32 (BitVec.zeroExtend 64 B * BitVec.zeroExtend 64 A) = Y
  have hXn : X.toNat = A.toNat * B.toNat % 2 ^ 32 * 0x77ffffff % 2 ^ 32 * BabyBearP / 2 ^ 32 := by
    rw [← hX, mulhu_toNat, hm]; rfl
  have hYn : Y.toNat = A.toNat * B.toNat / 2 ^ 32 := by rw [← hY, mulhu_toNat, Nat.mul_comm]
  have hZ : (if (0#32).ult (B * A) = true then 1#32 else 0#32).toNat =
      if A.toNat * B.toNat % 2 ^ 32 = 0 then 0 else 1 := by
    rw [← hlo]; split <;> rename_i h <;> simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_zero] at h <;>
      split <;> rename_i h' <;> simp_all
  generalize (if (0#32).ult (B * A) = true then 1#32 else 0#32) = Z at *
  clear hX hY hm hlo
  rw [Nat.add_mod, ← Nat.mod_eq_of_lt hc]
  generalize A.toNat * B.toNat = AB at *
  generalize AB * RINV % BabyBearP = R at *
  simp only [mask_sel]
  generalize AB % 2 ^ 32 * 2013265919 % 2 ^ 32 * BabyBearP / 2 ^ 32 = xN at *
  generalize AB / 2 ^ 32 = yN at *
  have hz1 : (if AB % 2 ^ 32 = 0 then 0 else 1) ≤ 1 := by split <;> simp
  generalize (if AB % 2 ^ 32 = 0 then 0 else 1) = zN at *
  simp only [BabyBearP] at *
  (by_cases hc1 : 2013265921 ≤ yN + xN + zN <;> simp only [hc1, ite_true, ite_false] at heq) <;>
    split <;> rename_i h1 <;> simp only [BitVec.ult, decide_eq_true_eq] at h1 <;>
    split <;> rename_i h2 <;> simp only [BitVec.ult, decide_eq_true_eq] at h2 <;> bv_omega
theorem bb_fma_mont (a b c r : Word) (h : r.toNat = (a.toNat * b.toNat * RINV + c.toNat) % BabyBearP) :
    mont r = mont a * mont b + mont c := by
  rw [mont_of_eq r _ h]; simp only [mont]; push_cast; ring

end RV
