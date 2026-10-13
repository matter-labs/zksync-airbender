import Slop.RV.AddMod
import Slop.RV.Code.mul_mod

/-! Mersenne31 `mul_mod`: 64-bit product split at bit 31, then a tail call into `add_mod`. -/

namespace RV

/-- `a0 ≤ P`, `a1 ≤ P` ⇒ result `≤ P` and `≡ a0 * a1 (mod P)`. -/
def mulModPost : State → State → Prop := fun s s' =>
  (s.r 10).toNat ≤ P → (s.r 11).toNat ≤ P →
    (s'.r 10).toNat ≤ P ∧ (s'.r 10).toNat % P = ((s.r 10).toNat * (s.r 11).toNat) % P

theorem mul_split (a b : Word) (ha : a.toNat ≤ P) (hb : b.toNat ≤ P) :
    ((b * a) <<< 1 >>> 1).toNat ≤ P ∧
    ((b * a) >>> 31 ||| BitVec.extractLsb' 32 32 (b.zeroExtend 64 * a.zeroExtend 64) <<< 1).toNat ≤ P ∧
    (((b * a) <<< 1 >>> 1).toNat +
      ((b * a) >>> 31 ||| BitVec.extractLsb' 32 32 (b.zeroExtend 64 * a.zeroExtend 64) <<< 1).toNat) % P =
      (a.toNat * b.toNat) % P := by
  simp only [P] at ha hb ⊢
  have hN : a.toNat * b.toNat ≤ 2147483647 * 2147483647 := Nat.mul_le_mul ha hb
  generalize hn : a.toNat * b.toNat = N at hN
  have hlo : (b * a).toNat = N % 2 ^ 32 := by rw [BitVec.toNat_mul, Nat.mul_comm, hn]
  have hhi : (BitVec.extractLsb' 32 32 (b.zeroExtend 64 * a.zeroExtend 64)).toNat = N / 2 ^ 32 := by
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    have ha' : a.toNat < 2 ^ 64 := by omega
    have hb' : b.toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb', Nat.mul_comm, hn]
    omega
  have hor : ∀ x y : Word, x.toNat < 2 → y.toNat % 2 = 0 → (x ||| y).toNat = x.toNat + y.toNat := by
    intro x y hx hy
    rw [← BitVec.add_eq_or_of_and_eq_zero, BitVec.toNat_add]
    · omega
    · ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_zero]
      by_cases h0 : i = 0
      · subst h0
        have : y[0] = false := by
          rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero]; simp [hy]
        simp [this]
      · have : x[i] = false := by
          rw [BitVec.getElem_eq_testBit_toNat]
          apply Nat.testBit_lt_two_pow
          calc x.toNat < 2 := hx
            _ = 2 ^ 1 := rfl
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
        simp [this]
  have h1 : ((b * a) <<< 1 >>> 1).toNat = N % 2 ^ 31 := by
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, hlo]
    omega
  have h2 : ((b * a) >>> 31).toNat = (N % 2 ^ 32) / 2 ^ 31 := by
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hlo]
  have h3 : (BitVec.extractLsb' 32 32 (b.zeroExtend 64 * a.zeroExtend 64) <<< 1).toNat = 2 * (N / 2 ^ 32) := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hhi]
    omega
  rw [hor _ _ (by rw [h2]; omega) (by rw [h3]; omega), h1, h2, h3]
  omega

/-- `mul_mod` at any address `A`, with `add_mod` where its tail call goes (`A - 0xc4`). -/
theorem mul_mod_impl (A : Word) (hlow : 0xc4 ≤ A.toNat) :
    ImplementsAt A Code.mul_mod [(A + 0xffffff3c#32, Code.add_mod)] 16 mulModPost := by
  intro s hentry hcallees hcall
  have hadd : CodeAt s (A + 0xffffff3c#32) Code.add_mod := hcallees (A + 0xffffff3c#32, Code.add_mod) (by simp)
  clear hcallees
  rw [Call, hentry] at hcall
  rv_start Code.mul_mod hcall
  rv_steps 15 with hentry
  apply run_call add_mod_impl
  · rv_call_ok hadd Code.add_mod
  rv_returned S1 hpc1 hpost1 hcs1 hmem1
  rv_ret
  refine ⟨hpc1, ?_, (by rv_callee with hcs1), (by rv_frame with hmem1)⟩
  intro ha hb
  simp only [BitVec.ofNat_eq_ofNat] at ha hb ⊢
  simp only [addModPost] at hpost1
  rv_regs at hpost1
  obtain ⟨hl, hh, he⟩ := mul_split (s.r 10#5) (s.r 11#5) ha hb
  obtain ⟨h1, h2⟩ := hpost1 hl hh
  exact ⟨h1, h2.trans he⟩

end RV
