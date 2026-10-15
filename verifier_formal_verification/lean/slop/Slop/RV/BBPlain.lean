import Slop.RV.BBMont
import Slop.Sym.Meta

/-! # Plain-Rust BabyBear arithmetic as the compiler emits it, for executor proofs

The executor's value DAG is cut at the results of the field operations (found by evaluation, `gen/`); each piece
between cuts is one of:
* a raw Montgomery product `T = hi + ⌊mp/2^32⌋ + carry` (`mm_cluster`, by `mm_raw`): `T < 2p`, `T ≡ xy·2^-32`;
* linear modular logic (add/sub with conditional correction, possibly fused): `lin_cluster`, by `omega`.
The values are then carried to `F` (`amN_cast`, `smN_cast`, `modp_cast`). -/

namespace RV
open Spec

/-- `mulhu`. -/
def mulhuW (x y : Word) : Word := (BitVec.zeroExtend 64 x * BitVec.zeroExtend 64 y).extractLsb' 32 32

@[bitvec_to_nat] theorem mulhuW_toNat (x y : Word) : (mulhuW x y).toNat = x.toNat * y.toNat / 2 ^ 32 :=
  mulhu_toNat x y

theorem mulhu_fold (x y : Word) : (BitVec.zeroExtend 64 x * BitVec.zeroExtend 64 y).extractLsb' 32 32 = mulhuW x y :=
  rfl

/-- The raw Montgomery product as `ops/basic.rs` `mul_mod` compiles: `hi + ⌊mp/2^32⌋ + carry(lo + mp mod 2^32)`, with
`m = lo · K`; below `2p` and `≡ xy · 2^-32 (mod p)`. -/
theorem mm_raw (x y : Word) (hy : y.toNat < BabyBearP) :
    let T := mulhuW x y + mulhuW (2013265919#32 * (x * y)) 2013265921#32 +
      (if (x * y + 2013265921#32 * (2013265919#32 * (x * y))).ult (2013265921#32 * (2013265919#32 * (x * y)))
        then 1 else 0)
    T.toNat < 2 * BabyBearP ∧ T.toNat % BabyBearP = x.toNat * y.toNat * RINV % BabyBearP := by
  intro T
  simp only [T]
  obtain ⟨h1, h2⟩ := mont_reduce x.toNat y.toNat x.isLt hy
  have key : ∀ t, t < 2 * BabyBearP → (if BabyBearP ≤ t then t - BabyBearP else t) = t % BabyBearP := by
    intro t ht; split <;> (simp only [BabyBearP] at *; omega)
  rw [key _ h1] at h2
  generalize hN : x.toNat * y.toNat = N at h1 h2
  have hlo : (x * y).toNat = N % 2 ^ 32 := by rw [BitVec.toNat_mul, hN]
  have hhi : (mulhuW x y).toNat = N / 2 ^ 32 := by rw [mulhuW_toNat, hN]
  generalize x * y = LO at *
  generalize mulhuW x y = HI at *
  have hm : (2013265919#32 * LO).toNat = N % 2 ^ 32 * 0x77ffffff % 2 ^ 32 := by
    rw [BitVec.toNat_mul, hlo, Nat.mul_comm]; rfl
  generalize 2013265919#32 * LO = M at *
  have hmh : (mulhuW M 2013265921#32).toNat = N % 2 ^ 32 * 0x77ffffff % 2 ^ 32 * BabyBearP / 2 ^ 32 := by
    rw [mulhuW_toNat, hm]; rfl
  have hml : (2013265921#32 * M).toNat = N % 2 ^ 32 * 0x77ffffff % 2 ^ 32 * BabyBearP % 2 ^ 32 := by
    rw [BitVec.toNat_mul, hm, Nat.mul_comm]; rfl
  generalize mulhuW M 2013265921#32 = MH at *
  generalize 2013265921#32 * M = ML at *
  clear hm
  -- `lo + ml ≡ 0`: the carry is `[lo ≠ 0]`
  have hz : (N % 2 ^ 32 + N % 2 ^ 32 * 0x77ffffff % 2 ^ 32 * BabyBearP % 2 ^ 32) % 2 ^ 32 = 0 := by
    generalize N % 2 ^ 32 = L; simp only [BabyBearP]; omega
  generalize N % 2 ^ 32 = L at *
  generalize N / 2 ^ 32 = H at *
  generalize L * 0x77ffffff % 2 ^ 32 * BabyBearP = MP at *
  have hc : (if (LO + ML).ult ML = true then (1 : Word) else 0).toNat = if L = 0 then 0 else 1 := by
    have : (LO + ML).toNat = 0 := by rw [BitVec.toNat_add, hlo, hml]; exact hz
    simp only [BitVec.ult, decide_eq_true_eq, this]
    split <;> split <;> simp_all <;> omega
  generalize (if (LO + ML).ult ML = true then (1 : Word) else 0) = CW at *
  have hT : (HI + MH + CW).toNat = H + MP / 2 ^ 32 + (if L = 0 then 0 else 1) := by
    have : (if L = 0 then 0 else 1) ≤ 1 := by split <;> simp
    simp only [BabyBearP] at *
    rw [BitVec.toNat_add, BitVec.toNat_add, hhi, hmh, hc]; omega
  rw [hT]; exact ⟨h1, h2⟩

/-- `to_u32`'s product by 1 (`lo = x`, no high part): `T ≤ p`, `T ≡ x · 2^-32`. -/
theorem mm_raw1 (x : Word) :
    let T := mulhuW (2013265919#32 * x) 2013265921#32 +
      (if (x + 2013265921#32 * (2013265919#32 * x)).ult (2013265921#32 * (2013265919#32 * x)) then 1 else 0)
    T.toNat ≤ BabyBearP ∧ T.toNat % BabyBearP = x.toNat * RINV % BabyBearP := by
  intro T
  simp only [T]
  have h := mm_raw x 1#32 (by decide)
  simp only [BitVec.mul_one] at h
  have hh : mulhuW x 1#32 = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [mulhuW_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mul_one]
    exact Nat.div_eq_of_lt x.isLt
  rw [hh, BitVec.zero_add] at h
  refine ⟨?_, by have h2 := h.2; rwa [show (1#32 : Word).toNat = 1 from rfl, Nat.mul_one] at h2⟩
  -- `⌊mp / 2^32⌋ ≤ p - 1` and the carry is at most 1
  have hmh : (mulhuW (2013265919#32 * x) 2013265921#32).toNat ≤ 2013265920 := by
    rw [mulhuW_toNat]; have := (2013265919#32 * x).isLt; simp only [BitVec.toNat_ofNat]; omega
  have hC : (if (x + 2013265921#32 * (2013265919#32 * x)).ult (2013265921#32 * (2013265919#32 * x)) = true
      then (1 : Word) else 0).toNat ≤ 1 := by split <;> simp
  rw [BitVec.toNat_add]; simp only [BabyBearP]; omega

/-- The branch-free select, mask on the right. -/
theorem mask_sel' (c : Bool) (k : Word) :
    k &&& (0#32 - (if c = true then (1 : Word) else 0)) = if c = true then k else 0 := by
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_decide

/-! Normal forms of the Montgomery constants' products (the DAG orders commutative arguments by node id). -/
theorem mulK_left (x : Word) : x * 2013265919#32 = 2013265919#32 * x := BitVec.mul_comm _ _
theorem mulP_left (x : Word) : x * 2013265921#32 = 2013265921#32 * x := BitVec.mul_comm _ _
theorem mulhuP_right (x : Word) : mulhuW 2013265921#32 x = mulhuW x 2013265921#32 := by
  simp only [mulhuW, BitVec.mul_comm]
theorem hi_mh_comm (z w : Word) :
    mulhuW (2013265919#32 * z) 2013265921#32 + w = w + mulhuW (2013265919#32 * z) 2013265921#32 :=
  BitVec.add_comm _ _

/-- The branch-free select `x & ([c] - 1)` (`to_u32`'s correction). -/
theorem and_sel (c : Bool) (x : Word) :
    x &&& ((if c = true then (1 : Word) else 0) + 4294967295#32) = if c = true then 0 else x := by
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_decide

/-- A raw Montgomery product node: `T < 2p ∧ T ≡ xy·2^-32` (goal after `sym_unfold`; `y < p` in context). -/
macro "mm_cluster" : tactic => `(tactic| (
  dsimp only [RV.alu, RV.mulhu_fold]
  simp only [RV.mulK_left, RV.mulP_left, RV.mulhuP_right, RV.hi_mh_comm]
  first | exact RV.mm_raw _ _ ‹_› | exact RV.mm_raw _ _ (by decide)))

/-- A raw Montgomery product by 1 (`to_u32`): `T ≤ p ∧ T ≡ x·2^-32`. -/
macro "mm1_cluster" : tactic => `(tactic| (
  dsimp only [RV.alu, RV.mulhu_fold]
  simp only [RV.mulK_left, RV.mulP_left, RV.mulhuP_right]
  exact RV.mm_raw1 _))

/-! Modular add / sub on canonical values, as `Nat`. -/
def amN (a b : Nat) : Nat := (a + b) % BabyBearP
def smN (a b : Nat) : Nat := (a + BabyBearP - b) % BabyBearP

/-- Linear modular logic between cuts (goal after `sym_unfold`; bounds of the cut values in context). -/
macro "lin_cluster" : tactic => `(tactic| (
  dsimp only [RV.alu, RV.amN, RV.smN]
  simp only [RV.mask_sel', RV.and_sel]
  split_ifs <;> simp only [BitVec.ult, decide_eq_true_eq] at * <;> simp only [RV.BabyBearP] at * <;> bv_omega))

/-! To `F`. -/
theorem modp_cast (t : Nat) : ((t % BabyBearP : Nat) : F) = t := natCast_mod_p t
theorem amN_cast (a b : Nat) : ((amN a b : Nat) : F) = a + b := by simp [amN, natCast_mod_p]
theorem smN_cast (a b : Nat) (hb : b ≤ BabyBearP) : ((smN a b : Nat) : F) = a - b := by
  simp only [smN, natCast_mod_p]; rw [Nat.cast_sub (by omega)]; push_cast; simp
theorem mm_F {t : Nat} {x y : Word} (h : t % BabyBearP = x.toNat * y.toNat * RINV % BabyBearP) :
    (t : F) * (RINV : F) = mont x * mont y := by
  have := congrArg (fun n : Nat => (n : F)) h
  simp only [natCast_mod_p] at this
  simp only [mont, this]; push_cast; ring

theorem ofLimbs_congr {a0 a1 a2 a3 b0 b1 b2 b3 : F} (h0 : a0 = b0) (h1 : a1 = b1) (h2 : a2 = b2) (h3 : a3 = b3) :
    ofLimbs a0 a1 a2 a3 = ofLimbs b0 b1 b2 b3 := by rw [h0, h1, h2, h3]

theorem mm1_F {t : Nat} {x : Word} (h : t % BabyBearP = x.toNat * RINV % BabyBearP) : (t : F) = mont x := by
  have := congrArg (fun n : Nat => (n : F)) h
  simp only [natCast_mod_p] at this
  simp only [mont, this]; push_cast; ring

/-- `new`: the product by `R² mod p` is the Montgomery form. -/
theorem new_F (y : Word) : mont y * mont 1172168163#32 = (y.toNat : F) := by
  have : (1172168163 : F) * (RINV : F) * (RINV : F) = 1 := by decide
  simp only [mont, BitVec.toNat_ofNat]; push_cast
  linear_combination (y.toNat : F) * this

theorem amN_lt (a b : Nat) : amN a b < BabyBearP := mod_p_lt _
theorem smN_lt (a b : Nat) : smN a b < BabyBearP := mod_p_lt _

end RV
