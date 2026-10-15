import Human.SpecExt4

/-! BabyBear in Montgomery form: what a register value means (`mont`), the field opcodes on it, and the Ext4
product formula. -/

namespace RV
open Spec Polynomial

/-- The field element a word holds in Montgomery form: `x · 2^-32`. -/
def mont (x : Word) : F := (x.toNat : F) * (RINV : F)

theorem RINV_mul : (RINV : F) * (2 ^ 32 : F) = 1 := by decide

theorem natCast_mod_p (n : Nat) : ((n % BabyBearP : Nat) : F) = n := ZMod.natCast_mod n _

theorem toNat_ofNat_lt (n : Nat) (h : n < BabyBearP) : (BitVec.ofNat 32 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by simp only [BabyBearP] at h ⊢; omega)

theorem mod_p_lt (n : Nat) : n % BabyBearP < BabyBearP := Nat.mod_lt _ (by decide)

theorem mopVal_lt (op : FieldOp) (a b o : Word) (h : op ≠ .triAdd) : (mopVal op a b o).toNat < BabyBearP := by
  cases op <;> simp only [mopVal] <;> first | exact absurd rfl h | rw [toNat_ofNat_lt _ (mod_p_lt _)]; exact mod_p_lt _

theorem mont_mul (a b o : Word) : mont (mopVal .mul a b o) = mont a * mont b := by
  simp only [mont, mopVal]
  rw [toNat_ofNat_lt _ (mod_p_lt _), natCast_mod_p]; push_cast [natCast_mod_p]; ring

theorem mont_fma (a b o : Word) : mont (mopVal .fma a b o) = mont a * mont b + mont o := by
  simp only [mont, mopVal]
  rw [toNat_ofNat_lt _ (mod_p_lt _), natCast_mod_p]; push_cast [natCast_mod_p]; ring

theorem mont_add (a b o : Word) : mont (mopVal .add a b o) = mont a + mont b := by
  simp only [mont, mopVal]
  rw [toNat_ofNat_lt _ (mod_p_lt _), natCast_mod_p]; push_cast [natCast_mod_p]; ring

theorem mont_sub (a b o : Word) : mont (mopVal .sub a b o) = mont a - mont b := by
  simp only [mont, mopVal]
  rw [toNat_ofNat_lt _ (mod_p_lt _), natCast_mod_p]
  have hb : b.toNat % BabyBearP ≤ BabyBearP := (mod_p_lt _).le
  push_cast [Nat.cast_sub (by omega : b.toNat % BabyBearP ≤ a.toNat % BabyBearP + BabyBearP), natCast_mod_p]
  simp only [ZMod.natCast_self]; ring

/-- `BabyBearField::NON_RES` (11 in Montgomery form), as the code loads it (`lui 0x38000; addi -0x17`). -/
theorem mont_nonres : mont 0x37ffffe9#32 = 11 := by decide

/-- `mul(x, 1)` (`to_u32`) gives the canonical value. -/
theorem mul_one_val (x o : Word) : ((mopVal .mul x 1#32 o).toNat : F) = mont x := by
  simp only [mont, mopVal]
  rw [toNat_ofNat_lt _ (mod_p_lt _), natCast_mod_p]; push_cast [natCast_mod_p]; simp

/-- `mul(v, R²)` (`new`) holds `v`. -/
theorem mont_new (v o : Word) : mont (mopVal .mul v 0x45dddde3#32 o) = (v.toNat : F) := by
  rw [mont_mul]; simp only [mont]
  have : ((0x45dddde3#32 : Word).toNat : F) * (RINV : F) * (RINV : F) = 1 := by decide
  linear_combination (v.toNat : F) * this

/-- An Ext4 element from 4 words in Montgomery form. -/
noncomputable def e4 (l0 l1 l2 l3 : Word) : E4 := ofLimbs (mont l0) (mont l1) (mont l2) (mont l3)

end RV

namespace Spec
open Polynomial

theorem w4 : w ^ 4 = 11 := by
  have h := AdjoinRoot.eval₂_root (X ^ 4 - C 11 : F[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [w, h]; rfl

/-- The Ext4 product on limbs (the table in `field/src/baby_bear/ext4.rs`, `mul_assign_flat_impl`). -/
theorem ofLimbs_mul (a0 a1 a2 a3 b0 b1 b2 b3 : F) :
    ofLimbs a0 a1 a2 a3 * ofLimbs b0 b1 b2 b3 =
      ofLimbs (a0 * b0 + 11 * (a1 * b1) + 11 * (a2 * b3) + 11 * (a3 * b2))
        (a0 * b1 + a1 * b0 + a2 * b2 + 11 * (a3 * b3))
        (a0 * b2 + 11 * (a1 * b3) + a2 * b0 + 11 * (a3 * b1))
        (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) := by
  simp only [ofLimbs, map_add, map_mul, map_ofNat]
  linear_combination (AdjoinRoot.of _ a1 * AdjoinRoot.of _ b1 + AdjoinRoot.of _ a2 * AdjoinRoot.of _ b3 +
    AdjoinRoot.of _ a3 * AdjoinRoot.of _ b2 +
    (AdjoinRoot.of _ a1 * AdjoinRoot.of _ b3 + AdjoinRoot.of _ a3 * AdjoinRoot.of _ b1) * w +
    AdjoinRoot.of _ a3 * AdjoinRoot.of _ b3 * w ^ 2) * w4

theorem ofLimbs_add (a0 a1 a2 a3 b0 b1 b2 b3 : F) :
    ofLimbs a0 a1 a2 a3 + ofLimbs b0 b1 b2 b3 = ofLimbs (a0 + b0) (a1 + b1) (a2 + b2) (a3 + b3) := by
  simp only [ofLimbs, map_add]; ring

end Spec
