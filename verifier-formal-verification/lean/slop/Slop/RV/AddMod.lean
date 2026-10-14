import Slop.RV.Tactic
import Slop.RV.Code.add_mod

/-! Mersenne31 `add_mod`, in `Nat` form (the `ZMod` statement is derived in `PolyFinal`). -/

namespace RV

/-- The Mersenne31 prime. -/
abbrev P : Nat := 2 ^ 31 - 1

/-- `a0 ≤ P`, `a1 ≤ P` ⇒ result `≤ P` and `≡ a0 + a1 (mod P)`. -/
def addModPost : State → State → Prop := fun s s' =>
  (s.getReg 10).toNat ≤ P → (s.getReg 11).toNat ≤ P →
    (s'.getReg 10).toNat ≤ P ∧ (s'.getReg 10).toNat % P = ((s.getReg 10).toNat + (s.getReg 11).toNat) % P

theorem add_mod_arith (a b : Word) (ha : a.toNat ≤ P) (hb : b.toNat ≤ P) :
    let sum := b + a
    (sum <<< 1 >>> 1 + sum >>> 31).toNat ≤ P ∧
    (sum <<< 1 >>> 1 + sum >>> 31).toNat % P = (a.toNat + b.toNat) % P := by
  intro sum
  simp only [P] at ha hb ⊢
  have hs : sum.toNat = a.toNat + b.toNat := by simp only [sum, BitVec.toNat_add]; omega
  have h1 : (sum <<< 1 >>> 1).toNat = sum.toNat % 2 ^ 31 := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    omega
  have h2 : (sum >>> 31).toNat = sum.toNat / 2 ^ 31 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h3 : (sum <<< 1 >>> 1 + sum >>> 31).toNat = sum.toNat % 2 ^ 31 + sum.toNat / 2 ^ 31 := by
    rw [BitVec.toNat_add, h1, h2]; omega
  rw [h3, hs]
  omega

theorem add_mod_impl : Implements Code.add_mod 16 addModPost := by
  intro s hcall
  rv_start Code.add_mod hcall
  rv_steps 13
  rv_ret
  refine ⟨by rv_regs, ?_, by rv_callee, by rv_frame⟩
  intro ha hb
  rv_regs
  exact add_mod_arith _ _ ha hb

end RV
