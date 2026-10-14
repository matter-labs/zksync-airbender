import Slop.RV.Mem

set_option linter.deprecated false

/-! A block copy of memory (`blockCopy m d s len`: `len` bytes from `s` to `d`) and how stores of loaded words build
it, for `memcpy`-like code: general in the addresses and the length, reusable for any copy loop. -/

namespace RV

/-- Memory `m` with `len` bytes copied from `s` to `d` (byte `a` of the copy: `a - d` bytes into it). -/
def blockCopy (m : Word → BitVec 8) (d s : Word) (len : Nat) : Word → BitVec 8 :=
  fun a => if (a - d).toNat < len then m (s + (a - d)) else m a

/-- Byte `b` after writing `n ≤ 4` bytes of `v` at `a`. -/
theorem write_apply (m : Word → BitVec 8) (a v : Word) (n : Nat) (hn : n ≤ 4) (b : Word) :
    write m a v n b = if (b - a).toNat < n then (v >>> (8 * (b - a).toNat)).setWidth 8 else m b := by
  induction n generalizing m a v with
  | zero => simp [write]
  | succ n ih =>
    simp only [write]
    rw [ih _ _ _ (by omega)]
    by_cases h0 : b = a
    · subst h0
      have e : (b - (b + 1)).toNat = 4294967295 := by bv_omega
      rw [e]
      simp [show ¬ (4294967295 < n) by omega]
    · have e : (b - (a + 1)).toNat = (b - a).toNat - 1 := by bv_omega
      have hpos : 0 < (b - a).toNat := by bv_omega
      rw [e]
      generalize (b - a).toNat = t at hpos ⊢
      by_cases h1 : t - 1 < n
      · simp only [h1, ↓reduceIte, show t < n + 1 by omega]
        rw [← BitVec.shiftRight_add, show 8 + 8 * (t - 1) = 8 * t by omega]
      · simp [h1, show ¬ t < n + 1 by omega, h0]

/-- Byte `k` of a read of `n ≤ 4` bytes. -/
theorem read_byte (m : Word → BitVec 8) (s : Word) (n k : Nat) (hn : n ≤ 4) (hk : k < n) :
    (read m s n >>> (8 * k)).setWidth 8 = m (s + BitVec.ofNat 32 k) := by
  induction n generalizing s k with
  | zero => omega
  | succ n ih =>
    simp only [read]
    cases k with
    | zero =>
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp [hj]
    | succ k =>
      rw [show s + BitVec.ofNat 32 (k + 1) = s + 1 + BitVec.ofNat 32 k by bv_omega, ← ih (s + 1) k (by omega) (by omega)]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      have h1 : 8 * (k + 1) + j < 32 := by omega
      have h2 : ¬ (8 * (k + 1) + j < 8) := by omega
      have e : 8 * (k + 1) + j - 8 = 8 * k + j := by omega
      simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hj, h1, h2, e,
        BitVec.getLsbD_of_ge (m s) _ (by omega : 8 ≤ 8 * (k + 1) + j)]
      rw [BitVec.getLsbD_eq_getElem (by omega)]

theorem blockCopy_zero (m : Word → BitVec 8) (d s : Word) : blockCopy m d s 0 = m := by
  funext a; simp [blockCopy]

/-- Copying `n ≤ 4` more bytes (read from the source memory `M`) extends a block copy. -/
theorem copy_step (M : Word → BitVec 8) (p q : Word) (k n : Nat) (hn : n ≤ 4) (hk : k + n < 2 ^ 32) :
    write (blockCopy M p q k) (p + BitVec.ofNat 32 k) (read M (q + BitVec.ofNat 32 k) n) n = blockCopy M p q (k + n) := by
  funext a
  rw [write_apply _ _ _ n hn]
  simp only [blockCopy]
  by_cases h : (a - (p + BitVec.ofNat 32 k)).toNat < n
  · have e : (a - p).toNat = k + (a - (p + BitVec.ofNat 32 k)).toNat := by bv_omega
    rw [if_pos h, read_byte _ _ _ _ hn h, if_pos (by omega)]
    congr 1; bv_omega
  · rw [if_neg h]
    by_cases h2 : (a - p).toNat < k
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by bv_omega)]

/-- The first `n ≤ 4` bytes of a copy. -/
theorem copy_first (M : Word → BitVec 8) (p q : Word) (n : Nat) (hn : n ≤ 4) :
    write M p (read M q n) n = blockCopy M p q n := by
  have := copy_step M p q 0 n hn (by omega)
  simpa [blockCopy_zero] using this

/-- Two block copies in a row (source and destination ranges disjoint, no wrap) are one block copy. -/
theorem blockCopy_append (m : Word → BitVec 8) (d s : Word) (k j : Nat) (hd : d.toNat + k + j ≤ 2 ^ 32)
    (hs : s.toNat + k + j ≤ 2 ^ 32) (hdisj : s.toNat + k + j ≤ d.toNat ∨ d.toNat + k + j ≤ s.toNat) :
    blockCopy (blockCopy m d s k) (d + BitVec.ofNat 32 k) (s + BitVec.ofNat 32 k) j = blockCopy m d s (k + j) := by
  funext a
  simp only [blockCopy]
  by_cases h : (a - (d + BitVec.ofNat 32 k)).toNat < j
  · have e : (a - d).toNat = k + (a - (d + BitVec.ofNat 32 k)).toNat := by bv_omega
    rw [if_pos h, if_neg (by bv_omega), if_pos (by omega)]
    congr 1; bv_omega
  · rw [if_neg h]
    by_cases h2 : (a - d).toNat < k
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by bv_omega)]

theorem blockCopy_outside (m : Word → BitVec 8) (d s a : Word) (len : Nat) (h : len ≤ (a - d).toNat) :
    blockCopy m d s len a = m a := by
  simp only [blockCopy, if_neg (show ¬ (a - d).toNat < len by omega)]

/-- Reads outside the destination see the memory before the copy. -/
theorem read_blockCopy_outside (m : Word → BitVec 8) (d s c : Word) (len n : Nat)
    (h : c.toNat + n ≤ d.toNat ∨ d.toNat + len ≤ c.toNat) (hc : c.toNat + n ≤ 2 ^ 32) (hd : d.toNat + len ≤ 2 ^ 32) :
    read (blockCopy m d s len) c n = read m c n := by
  apply read_congr
  intro j hj
  apply blockCopy_outside
  bv_omega

/-- `lh` + `sh`: the sign extension of a 2-byte load does not change the 2 bytes stored. -/
theorem write_signExtend2 (m : Word → BitVec 8) (a x : Word) :
    write m a ((x.setWidth (8 * 2)).signExtend 32) 2 = write m a x 2 := by
  funext b
  rw [write_apply _ _ _ 2 (by omega), write_apply _ _ _ 2 (by omega)]
  split
  · rename_i h
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and,
      BitVec.getLsbD_signExtend]
    generalize (b - a).toNat = t at h
    have h1 : 8 * t + j < 16 := by omega
    have h2 : 8 * t + j < 32 := by omega
    simp [h1, h2]
  · rfl

end RV
