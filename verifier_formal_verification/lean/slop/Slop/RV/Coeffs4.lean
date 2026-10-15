import Slop.RV.Ext4Call
import Slop.RV.Code.COEFFS4

/-! The Ext4 coefficient table `COEFFS4`: 32 elements, 4 Montgomery-form limbs each, holding `Spec.coeff4 i`. -/

namespace RV
open Spec

set_option maxRecDepth 10000 in
theorem coeffs4_length : Code.COEFFS4.length = 128 := rfl

/-- Limb `k` of `coeff4 i` (canonical): `(i + 1, 2 i + 3, i², 7)`. -/
def coeff4Limb (i k : Nat) : Nat := match k with | 0 => i + 1 | 1 => 2 * i + 3 | 2 => i ^ 2 | _ => 7

/-- Every table word is canonical and holds its limb (checked by the kernel, word by word). -/
theorem coeffs4_check : (List.range 128).all (fun j => decide ((Code.COEFFS4[j]!).toNat < BabyBearP ∧
    (Code.COEFFS4[j]!).toNat * RINV % BabyBearP = coeff4Limb (j / 4) (j % 4) % BabyBearP)) = true := by
  decide +kernel

theorem coeffs4_word (j : Nat) (hj : j < 128) : (Code.COEFFS4[j]!).toNat < BabyBearP ∧
    mont (Code.COEFFS4[j]!) = (coeff4Limb (j / 4) (j % 4) : F) := by
  have := List.all_eq_true.mp coeffs4_check j (List.mem_range.mpr hj)
  rw [decide_eq_true_eq] at this
  refine ⟨this.1, ?_⟩
  simp only [mont]
  rw [← Nat.cast_mul, ← ZMod.natCast_mod, this.2, ZMod.natCast_mod]

/-- The table in memory at `T`: element `i` is canonical and is `coeff4 i`. -/
theorem table4 {m : Word → BitVec 8} {T : Word} (h : CodeMem m T Code.COEFFS4) (i : Nat) (hi : i < 32) :
    canon4 m (T + BitVec.ofNat 32 (16 * i)) ∧ e4At m (T + BitVec.ofNat 32 (16 * i)) = coeff4 i := by
  have hr : ∀ k < 4, read m (T + BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 (4 * k)) 4 = Code.COEFFS4[4 * i + k]! := by
    intro k hk
    rw [getElem!_pos Code.COEFFS4 (4 * i + k) (by rw [coeffs4_length]; omega), ← h (4 * i + k)
      (by rw [coeffs4_length]; omega)]
    congr 1; rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  have h0 := hr 0 (by omega); have h1 := hr 1 (by omega); have h2 := hr 2 (by omega); have h3 := hr 3 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, BitVec.add_zero] at h0 h1 h2 h3
  have w0 := coeffs4_word (4 * i) (by omega); have w1 := coeffs4_word (4 * i + 1) (by omega)
  have w2 := coeffs4_word (4 * i + 2) (by omega); have w3 := coeffs4_word (4 * i + 3) (by omega)
  simp only [show 4 * i / 4 = i by omega, show (4 * i + 1) / 4 = i by omega, show (4 * i + 2) / 4 = i by omega,
    show 4 * i % 4 = 0 by omega, show (4 * i + 1) % 4 = 1 by omega,
    show (4 * i + 2) % 4 = 2 by omega, show (4 * i + 3) % 4 = 3 by omega, coeff4Limb, Nat.add_zero] at w0 w1 w2 w3
  simp only [canon4, e4At, e4, h0, h1, h2, h3, w0.1, w1.1, w2.1, w3.1, w0.2, w1.2, w2.2, w3.2, coeff4, true_and]
  simp only [Nat.cast_ofNat]

end RV

namespace RV
open Spec

/-- An Ext4 element from 4 canonical words (no Montgomery form): what `ext4_poly` reads and writes. -/
noncomputable def limbsAt (m : Word → BitVec 8) (p : Word) : E4 :=
  ofLimbs ((read m p 4).toNat : F) ((read m (p + 4#32) 4).toNat : F) ((read m (p + 8#32) 4).toNat : F)
    ((read m (p + 12#32) 4).toNat : F)

/-- `ext4_poly(out = a0, y = a1)`: 16 bytes each in RAM above `sp`, `y` canonical; the
coefficient table in RAM at `0x1400190` (where `init` copies it), above `sp`. -/
def e4polyPre (s : State) : Prop :=
  argOk (s.getReg 2#5) (s.getReg 10#5) ∧ argOk (s.getReg 2#5) (s.getReg 11#5) ∧ canon4 s.mem (s.getReg 11#5) ∧
  CodeMem s.mem 0x1400190#32 Code.COEFFS4 ∧ (s.getReg 2#5).toNat ≤ 0x1400190

/-- `out ← poly4 y`, canonical. -/
def e4polyPost (s s' : State) : Prop :=
  canon4 s'.mem (s.getReg 10#5) ∧ limbsAt s'.mem (s.getReg 10#5) = poly4 (limbsAt s.mem (s.getReg 11#5))

end RV
