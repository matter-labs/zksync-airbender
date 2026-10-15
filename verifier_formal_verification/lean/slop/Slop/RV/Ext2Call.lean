import Slop.RV.Ext4Call
import Slop.RV.BBAddSub
import Slop.RV.BBMul

/-! Contracts of the plain-Rust Ext2/Ext4 functions, and the base ops' results as field elements. -/

namespace RV
open Spec

/-- An Ext2 element at `p` (8 bytes, Montgomery limbs `c0 + c1 v`, `v = w²`), inside Ext4. -/
noncomputable def e2At (m : Word → BitVec 8) (p : Word) : E4 :=
  ofLimbs (mont (read m p 4)) (mont (read m (p + 4#32) 4)) 0 0

def canon2 (m : Word → BitVec 8) (p : Word) : Prop :=
  (read m p 4).toNat < BabyBearP ∧ (read m (p + 4#32) 4).toNat < BabyBearP

/-- `ext2_mul_assign(a = a0, b = a1)`: both 8 bytes in RAM above `sp`, canonical. -/
def ext2MulPre (s : State) : Prop :=
  argOk (s.getReg 2#5) (s.getReg 10#5) ∧ argOk (s.getReg 2#5) (s.getReg 11#5) ∧
  canon2 s.mem (s.getReg 10#5) ∧ canon2 s.mem (s.getReg 11#5)

/-- `a ← a · b`, canonical. -/
def ext2MulPost (s s' : State) : Prop :=
  canon2 s'.mem (s.getReg 10#5) ∧ e2At s'.mem (s.getReg 10#5) = e2At s.mem (s.getReg 10#5) * e2At s.mem (s.getReg 11#5)

/-! The base ops on Montgomery values. -/

theorem mont_of_eq (r : Word) (n : Nat) (h : r.toNat = n % BabyBearP) : mont r = (n : F) * RINV := by
  simp only [mont, h, natCast_mod_p]

theorem bb_add_mont (a b r : Word) (h : r.toNat = (a.toNat + b.toNat) % BabyBearP) : mont r = mont a + mont b := by
  rw [mont_of_eq r _ h]; simp only [mont]; push_cast; ring

theorem bb_sub_mont (a b r : Word) (hb : b.toNat < BabyBearP)
    (h : r.toNat = (a.toNat + BabyBearP - b.toNat) % BabyBearP) : mont r = mont a - mont b := by
  rw [mont_of_eq r _ h]; simp only [mont]
  rw [Nat.cast_sub (by omega)]; push_cast; simp only [ZMod.natCast_self]; ring

theorem bb_mul_mont (a b r : Word) (h : r.toNat = a.toNat * b.toNat * RINV % BabyBearP) :
    mont r = mont a * mont b := by
  rw [mont_of_eq r _ h]; simp only [mont]; push_cast; ring

theorem lt_of_eq_mod (r : Word) (n : Nat) (h : r.toNat = n % BabyBearP) : r.toNat < BabyBearP := by
  rw [h]; exact mod_p_lt n

end RV
