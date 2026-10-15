import Slop.RV.CallW
import Slop.RV.BB

/-! The contract of the Ext4 functions: elements as 4 words in memory (Montgomery form, canonical). -/

namespace RV
open Spec

/-- The Ext4 element at `p` (16 bytes). -/
noncomputable def e4At (m : Word → BitVec 8) (p : Word) : E4 :=
  e4 (read m p 4) (read m (p + 4#32) 4) (read m (p + 8#32) 4) (read m (p + 12#32) 4)

/-- Its 4 limbs are canonical (`< p`). -/
def canon4 (m : Word → BitVec 8) (p : Word) : Prop :=
  (read m p 4).toNat < BabyBearP ∧ (read m (p + 4#32) 4).toNat < BabyBearP ∧
  (read m (p + 8#32) 4).toNat < BabyBearP ∧ (read m (p + 12#32) 4).toNat < BabyBearP

/-- 16 bytes at `p`, 4-aligned, in RAM at or above `sp` (outside the callee's frame). -/
def argOk (sp p : Word) : Prop := p.toNat % 4 = 0 ∧ sp.toNat ≤ p.toNat ∧ p.toNat + 16 ≤ RAM_END

/-- Rust `&mut` vs `&`: the regions do not overlap. -/
def disj16 (p q : Word) : Prop := p.toNat + 16 ≤ q.toNat ∨ q.toNat + 16 ≤ p.toNat

/-- `ext4_mul_add(acc = a0, x = a1, c = a2)`: canonical arguments in RAM, `acc` apart from `x` and `c`. -/
def mulAddPre (s : State) : Prop :=
  argOk (s.getReg 2#5) (s.getReg 10#5) ∧ argOk (s.getReg 2#5) (s.getReg 11#5) ∧ argOk (s.getReg 2#5) (s.getReg 12#5) ∧
  disj16 (s.getReg 10#5) (s.getReg 11#5) ∧ disj16 (s.getReg 10#5) (s.getReg 12#5) ∧
  canon4 s.mem (s.getReg 10#5) ∧ canon4 s.mem (s.getReg 11#5) ∧ canon4 s.mem (s.getReg 12#5)

/-- `acc ← acc · x + c`, canonical. -/
def mulAddPost (s s' : State) : Prop :=
  canon4 s'.mem (s.getReg 10#5) ∧
  e4At s'.mem (s.getReg 10#5) = e4At s.mem (s.getReg 10#5) * e4At s.mem (s.getReg 11#5) + e4At s.mem (s.getReg 12#5)

end RV

namespace RV
open Spec

/-- Reading 16 bytes only depends on those bytes. -/
theorem read16_congr {m m' : Word → BitVec 8} {p : Word} (hp : p.toNat + 16 ≤ 2 ^ 32)
    (h : ∀ a : Word, p.toNat ≤ a.toNat → a.toNat < p.toNat + 16 → m' a = m a) (k : Word) (hk : k.toNat + 4 ≤ 16) :
    read m' (p + k) 4 = read m (p + k) 4 := by
  apply read_congr; intro j hj; apply h <;> bv_omega

theorem e4At_congr {m m' : Word → BitVec 8} {p : Word} (hp : p.toNat + 16 ≤ 2 ^ 32)
    (h : ∀ a : Word, p.toNat ≤ a.toNat → a.toNat < p.toNat + 16 → m' a = m a) :
    e4At m' p = e4At m p ∧ (canon4 m' p ↔ canon4 m p) := by
  have h0 := read16_congr hp h 0#32 (by decide)
  rw [BitVec.add_zero] at h0
  simp only [e4At, canon4, h0, read16_congr hp h 4#32 (by decide), read16_congr hp h 8#32 (by decide),
    read16_congr hp h 12#32 (by decide), and_self]

/-- Horner's rule from the top coefficient, after `j` of `n` steps: `∑_{i < j} C (n - j + i) xⁱ`. -/
noncomputable def hornerAcc (C : ℕ → E4) (x : E4) (n : ℕ) : ℕ → E4
  | 0 => 0
  | j + 1 => hornerAcc C x n j * x + C (n - j - 1)

theorem hornerAcc_eq (C : ℕ → E4) (x : E4) (n : ℕ) :
    ∀ j ≤ n, hornerAcc C x n j = ∑ i ∈ Finset.range j, C (n - j + i) * x ^ i := by
  intro j
  induction j with
  | zero => intro; simp [hornerAcc]
  | succ j ih =>
    intro hj
    rw [hornerAcc, ih (by omega), Finset.sum_range_succ', Finset.sum_mul]
    simp only [pow_zero, mul_one, pow_succ, ← mul_assoc]
    congr 1
    · apply Finset.sum_congr rfl; intro i _; rw [show n - (j + 1) + (i + 1) = n - j + i by omega]

theorem hornerAcc_step (C : ℕ → E4) (x : E4) (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    hornerAcc C x n (n - k) * x + C (k - 1) = hornerAcc C x n (n - (k - 1)) := by
  rw [show n - (k - 1) = (n - k) + 1 by omega, hornerAcc, show n - (n - k) - 1 = k - 1 by omega]

theorem hornerAcc_full (C : ℕ → E4) (x : E4) (n : ℕ) :
    hornerAcc C x n n = ∑ i ∈ Finset.range n, C i * x ^ i := by
  rw [hornerAcc_eq C x n n le_rfl]; simp

end RV

namespace RV
open Spec

/-- `ext4_horner(out = a0, coeffs = a1, n = a2, x = a3)`: `out` and `x` 16 bytes, the `n` coefficients (16 bytes each)
in RAM above `sp`; `x` and the coefficients canonical. -/
def hornerPre (s : State) : Prop :=
  argOk (s.getReg 2#5) (s.getReg 10#5) ∧ argOk (s.getReg 2#5) (s.getReg 13#5) ∧ canon4 s.mem (s.getReg 13#5) ∧
  (s.getReg 11#5).toNat % 4 = 0 ∧ (s.getReg 2#5).toNat ≤ (s.getReg 11#5).toNat ∧
  (s.getReg 11#5).toNat + 16 * (s.getReg 12#5).toNat ≤ RAM_END ∧
  ∀ i < (s.getReg 12#5).toNat, canon4 s.mem (s.getReg 11#5 + BitVec.ofNat 32 (16 * i))

/-- `out ← ∑_{i < n} cᵢ xⁱ`, canonical. -/
def hornerPost (s s' : State) : Prop :=
  canon4 s'.mem (s.getReg 10#5) ∧
  e4At s'.mem (s.getReg 10#5) = ∑ i ∈ Finset.range (s.getReg 12#5).toNat,
    e4At s.mem (s.getReg 11#5 + BitVec.ofNat 32 (16 * i)) * e4At s.mem (s.getReg 13#5) ^ i

theorem e4_zero : e4 0#32 0#32 0#32 0#32 = 0 := by
  simp [e4, mont, ofLimbs]

end RV
