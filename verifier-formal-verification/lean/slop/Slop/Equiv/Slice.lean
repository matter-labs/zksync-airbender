import Mathlib.Data.Nat.Bitwise
import Sail

/-! Bit-slice facts for walking Sail's decoder: a guard `extractLsb w hi lo == c` is decided from what is known
about a few bits of `w`, with one general lemma (each use: a closed check on small numbers). -/

namespace Slop.Equiv

/-- Bits `[lo, lo + n)` of `w` are `k`. -/
def Bits (w : BitVec 32) (lo n k : Nat) : Prop := (w.toNat >>> lo) % 2 ^ n = k

/-- Bits `[lo + d, lo + d + n)` of `x`, read through the slice `[lo, lo + m)`. -/
theorem slice_of_slice (x lo m d n : Nat) (h : d + n ≤ m) :
    ((((x >>> lo) % 2 ^ m) >>> d) % 2 ^ n) = ((x >>> (lo + d)) % 2 ^ n) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hj : j < n
  · have : d + j < m := by omega
    simp [hj, this, Nat.add_assoc]
  · simp [hj]

/-- If bits `[lo', lo' + n)` of `w` are known to be `k`, a guard comparing an enclosing slice `[lo, hi]` with a
constant `c` whose corresponding bits differ from `k` is false. -/
theorem slice_beq_false {w : BitVec 32} {hi lo : Nat} {c : BitVec (hi - lo + 1)} (lo' n k : Nat)
    (hk : Bits w lo' n k) (hlo : lo ≤ lo') (hhi : lo' + n ≤ hi + 1)
    (hc : ((c.toNat >>> (lo' - lo)) % 2 ^ n) ≠ k) : (Sail.BitVec.extractLsb w hi lo == c) = false := by
  rw [beq_eq_false_iff_ne]
  intro he
  apply hc
  rw [← he, ← (hk : ((w.toNat >>> lo') % 2 ^ n) = k)]
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat]
  rw [slice_of_slice _ _ _ _ _ (by omega)]
  congr 2; omega

/-- The same slice, fully known: the guard is true. -/
theorem slice_beq_true {w : BitVec 32} {hi lo : Nat} {c : BitVec (hi - lo + 1)}
    (hk : Bits w lo (hi - lo + 1) c.toNat) : (Sail.BitVec.extractLsb w hi lo == c) = true := by
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat]
  exact hk

/-- A whole-word guard `w == c`, decided from known bits. -/
theorem word_beq_false {w c : BitVec 32} (lo n k : Nat) (hk : Bits w lo n k)
    (hc : ((c.toNat >>> lo) % 2 ^ n) ≠ k) : (w == c) = false := by
  rw [beq_eq_false_iff_ne]
  intro he; subst he; exact hc hk

/-- A fully known slice is a literal. -/
theorem slice_eq_lit {w : BitVec 32} {hi lo : Nat} (k : Nat) (hk : Bits w lo (hi - lo + 1) k) :
    Sail.BitVec.extractLsb w hi lo = BitVec.ofNat (hi - lo + 1) k := by
  apply BitVec.eq_of_toNat_eq
  have hk' : ((w.toNat >>> lo) % 2 ^ (hi - lo + 1)) = k := hk
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, hk']
  rw [← hk', Nat.mod_mod]

/-- Known bits give known sub-slices. -/
theorem bits_sub {w : BitVec 32} {lo n k : Nat} (lo' n' : Nat) (h : Bits w lo n k) (h1 : lo ≤ lo')
    (h2 : lo' + n' ≤ lo + n) : Bits w lo' n' ((k >>> (lo' - lo)) % 2 ^ n') := by
  have h' : ((w.toNat >>> lo) % 2 ^ n) = k := h
  show ((w.toNat >>> lo') % 2 ^ n') = _
  rw [← h', slice_of_slice _ _ _ _ _ (by omega)]
  congr 2; omega

end Slop.Equiv
