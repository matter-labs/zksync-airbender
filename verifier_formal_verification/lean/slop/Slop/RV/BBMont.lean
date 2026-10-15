import Slop.RV.BB

/-! Lemmas for the plain-Rust BabyBear ops (`ops/basic.rs`): Montgomery reduction with `mul`/`mulhu`, and the
branch-free conditional the compiler emits. -/

namespace RV
open Spec

/-- `MONT_K = -p⁻¹ mod 2^32`. -/
theorem mont_k_spec : (1 + 0x77ffffff * BabyBearP) % 2 ^ 32 = 0 := by decide

/-- Montgomery reduction as `bb_mul` computes it (`basic.rs` `mul_mod`): with `lo = ab mod 2^32` and
`m = lo · K mod 2^32`, `t = ⌊ab / 2^32⌋ + ⌊mp / 2^32⌋ + [lo ≠ 0]` is `(ab + mp) / 2^32`, below `2p`, and one
conditional subtraction gives `ab · 2^-32 mod p`. -/
theorem mont_reduce (a b : Nat) (ha : a < 2 ^ 32) (hb : b < BabyBearP) :
    let lo := a * b % 2 ^ 32
    let m := lo * 0x77ffffff % 2 ^ 32
    let t := a * b / 2 ^ 32 + m * BabyBearP / 2 ^ 32 + (if lo = 0 then 0 else 1)
    t < 2 * BabyBearP ∧ (if BabyBearP ≤ t then t - BabyBearP else t) = a * b * RINV % BabyBearP := by
  intro lo m t
  -- `ab + mp ≡ 0 (mod 2^32)`
  have hdiv : (a * b + m * BabyBearP) % 2 ^ 32 = 0 := by
    have : ((a * b + m * BabyBearP : Nat) : ZMod (2 ^ 32)) = 0 := by
      simp only [m, lo, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod]
      have hk : ((1 + 0x77ffffff * BabyBearP : Nat) : ZMod (2 ^ 32)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero mont_k_spec
      push_cast at hk
      linear_combination ((a : ZMod (2 ^ 32)) * b) * hk
    rw [ZMod.natCast_eq_zero_iff] at this; exact Nat.mod_eq_zero_of_dvd this
  -- `t · 2^32 = ab + mp`, `t < 2p`
  have hab : a * b < 2 ^ 32 * BabyBearP := Nat.mul_lt_mul_of_lt_of_le ha hb.le (by decide)
  have hm : m < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hmp : m * BabyBearP < 2 ^ 32 * BabyBearP := Nat.mul_lt_mul_of_pos_right hm (by decide)
  have ht : t * 2 ^ 32 = a * b + m * BabyBearP := by
    simp only [t, lo] at *
    generalize a * b = AB at *
    generalize m * BabyBearP = MP at *
    split <;> omega
  have hlt : t < 2 * BabyBearP := by simp only [BabyBearP] at *; omega
  refine ⟨hlt, ?_⟩
  -- modulo `p`: `t ≡ ab · 2^-32`
  have hz : (t : ZMod BabyBearP) = (a * b * RINV : Nat) := by
    have h1 := congrArg (fun n : Nat => (n : ZMod BabyBearP)) ht
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero] at h1
    have hr : (RINV : ZMod BabyBearP) * 2 ^ 32 = 1 := RINV_mul
    push_cast
    linear_combination (RINV : ZMod BabyBearP) * h1 - (t : ZMod BabyBearP) * hr
  have heq : (if BabyBearP ≤ t then t - BabyBearP else t) = t % BabyBearP := by
    clear_value t; split <;> (simp only [BabyBearP] at *; omega)
  rw [heq, ← ZMod.val_natCast, hz, ZMod.val_natCast]
/-- The branch-free select the compiler emits: `(0 - [c]) & k`. -/
theorem mask_sel (c : Bool) (k : Word) : (0#32 - (if c = true then 1#32 else 0#32)) &&& k = if c = true then k else 0#32 := by
  cases c <;> simp; exact BitVec.allOnes_and

theorem mulhu_toNat (x y : Word) :
    (BitVec.extractLsb' 32 32 (BitVec.zeroExtend 64 x * BitVec.zeroExtend 64 y)).toNat = x.toNat * y.toNat / 2 ^ 32 := by
  have hx := x.isLt; have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_le hx hy.le (by decide)
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : x.toNat * y.toNat < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul hxy)

/-! The base ops on Montgomery values. -/

theorem mont_of_eq (r : Word) (n : Nat) (h : r.toNat = n % BabyBearP) : mont r = (n : F) * RINV := by
  simp only [mont, h, natCast_mod_p]

theorem bb_add_mont (a b r : Word) (h : r.toNat = (a.toNat + b.toNat) % BabyBearP) : mont r = mont a + mont b := by
  rw [mont_of_eq r _ h]; simp only [mont]; push_cast; ring

theorem bb_mul_mont (a b r : Word) (h : r.toNat = a.toNat * b.toNat * RINV % BabyBearP) :
    mont r = mont a * mont b := by
  rw [mont_of_eq r _ h]; simp only [mont]; push_cast; ring

theorem lt_of_eq_mod (r : Word) (n : Nat) (h : r.toNat = n % BabyBearP) : r.toNat < BabyBearP := by
  rw [h]; exact mod_p_lt n

end RV

namespace RV
open Spec

/-- `mul(y, R²)` in plain Rust (`new`): holds `y`. -/
theorem mont_new_plain (y r : Word) (h : r.toNat = y.toNat * 1172168163 * RINV % BabyBearP) :
    mont r = (y.toNat : F) := by
  rw [mont_of_eq r _ h]; push_cast
  have : (1172168163 : F) * (RINV : F) * (RINV : F) = 1 := by decide
  linear_combination (y.toNat : F) * this

/-- `mul(x, 1)` in plain Rust (`to_u32`): the canonical value. -/
theorem val_to_u32_plain (x r : Word) (h : r.toNat = x.toNat * 1 * RINV % BabyBearP) :
    (r.toNat : F) = mont x := by
  rw [h, natCast_mod_p]; simp [mont]

end RV
