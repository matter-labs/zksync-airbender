import Slop.RV.Mem

/-! # Memory facts at base-plus-offset addresses, with Nat side conditions

A block's accesses are `base + k` for a register `base` and constant offsets `k`. The side conditions of
`read_write_disjoint` / `write_outside` are then linear facts about the offsets, so `omega` discharges them (instead of
`bv_omega` on each instance). Proven once; use with `simp (disch := omega) only [...]` or `rw` then `omega`. -/

namespace RV

/-- An offset address does not wrap (`x + k < 2³²`): its `toNat` is the sum. -/
theorem toNat_base (x : Word) (k : Nat) (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  have := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A store of `n` bytes at `base + k1` does not change a read of `r` bytes at `base + k2` when the two ranges are
disjoint (Nat offsets, no wrap). -/
theorem read_write_base (m : Word → BitVec 8) (x v : Word) (k1 n k2 r : Nat)
    (h : k2 + r ≤ k1 ∨ k1 + n ≤ k2) (hn : 0 < n) (hr : 0 < r)
    (ha : x.toNat + k1 + n ≤ 2 ^ 32) (hc : x.toNat + k2 + r ≤ 2 ^ 32) :
    read (write m (x + BitVec.ofNat 32 k1) v n) (x + BitVec.ofNat 32 k2) r = read m (x + BitVec.ofNat 32 k2) r := by
  apply read_write_disjoint
  · rw [toNat_base x k1 (by omega), toNat_base x k2 (by omega)]; omega
  · rw [toNat_base x k1 (by omega)]; omega
  · rw [toNat_base x k2 (by omega)]; omega

/-- A store of `n` bytes at `base + k` leaves the byte at `b` unchanged when `b` is outside its range. -/
theorem write_base_outside (m : Word → BitVec 8) (x v b : Word) (k n : Nat) (hn : 0 < n)
    (h : b.toNat < x.toNat + k ∨ x.toNat + k + n ≤ b.toNat) (ha : x.toNat + k + n ≤ 2 ^ 32) :
    write m (x + BitVec.ofNat 32 k) v n b = m b := by
  apply write_outside
  · rw [toNat_base x k (by omega)]; omega
  · rw [toNat_base x k (by omega)]; omega

/-- The `N` words at `base + k0` are unchanged by a store of `n` bytes at `base + k` outside them. -/
theorem readWords_base_write (m : Word → BitVec 8) (x v : Word) (k n k0 N : Nat)
    (h : k + n ≤ k0 ∨ k0 + 4 * N ≤ k) (hn : 0 < n) (ha : x.toNat + k + n ≤ 2 ^ 32)
    (hc : x.toNat + k0 + 4 * N ≤ 2 ^ 32) :
    Vector.ofFn (fun i : Fin N => read (write m (x + BitVec.ofNat 32 k) v n)
      (x + BitVec.ofNat 32 k0 + BitVec.ofNat 32 (4 * i.val)) 4) =
      Vector.ofFn (fun i : Fin N => read m (x + BitVec.ofNat 32 k0 + BitVec.ofNat 32 (4 * i.val)) 4) := by
  apply Vector.ext; intro i hi; simp only [Vector.getElem_ofFn]
  have hi' : i < N := hi
  rw [show x + BitVec.ofNat 32 k0 + BitVec.ofNat 32 (4 * i) = x + BitVec.ofNat 32 (k0 + 4 * i) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]
  exact read_write_base m x v k n (k0 + 4 * i) 4 (by omega) hn (by omega) ha (by omega)
/-- A store of `n` bytes at `base + k` does not change a read of `r` bytes at any address `c` outside its range. -/
theorem read_write_at (m : Word → BitVec 8) (x v c : Word) (k n r : Nat) (hn : 0 < n) (hr : 0 < r)
    (h : c.toNat + r ≤ x.toNat + k ∨ x.toNat + k + n ≤ c.toNat)
    (ha : x.toNat + k + n ≤ 2 ^ 32) (hc : c.toNat + r ≤ 2 ^ 32) :
    read (write m (x + BitVec.ofNat 32 k) v n) c r = read m c r := by
  apply read_write_disjoint
  · rw [toNat_base x k (by omega)]; omega
  · rw [toNat_base x k (by omega)]; omega
  · omega

/-- An offset address `base + k` whose sum with `base` wraps past `2³²`: its `toNat` is `base + k - 2³²`. -/
theorem toNat_wrap (x : Word) (k : Nat) (hk : k < 2 ^ 32) (hw : 2 ^ 32 ≤ x.toNat + k) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k - 2 ^ 32 := by
  have := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A store at a wrapped offset (e.g. `sp - 4`, written as `sp + (2³² - 4)`) does not change a read outside it. -/
theorem read_write_wrap (m : Word → BitVec 8) (x v c : Word) (k n r : Nat) (hn : 0 < n) (hr : 0 < r)
    (hk : k < 2 ^ 32) (hw : 2 ^ 32 ≤ x.toNat + k)
    (h : c.toNat + r ≤ x.toNat + k - 2 ^ 32 ∨ x.toNat + k - 2 ^ 32 + n ≤ c.toNat)
    (ha : x.toNat + k - 2 ^ 32 + n ≤ 2 ^ 32) (hc : c.toNat + r ≤ 2 ^ 32) :
    read (write m (x + BitVec.ofNat 32 k) v n) c r = read m c r := by
  apply read_write_disjoint
  · rw [toNat_wrap x k hk hw]; omega
  · rw [toNat_wrap x k hk hw]; omega
  · omega

/-- Memory at `c` outside a wrapped store is unchanged. -/
theorem write_wrap_outside (m : Word → BitVec 8) (x v c : Word) (k n : Nat) (hn : 0 < n) (hk : k < 2 ^ 32)
    (hw : 2 ^ 32 ≤ x.toNat + k)
    (h : c.toNat < x.toNat + k - 2 ^ 32 ∨ x.toNat + k - 2 ^ 32 + n ≤ c.toNat)
    (ha : x.toNat + k - 2 ^ 32 + n ≤ 2 ^ 32) :
    write m (x + BitVec.ofNat 32 k) v n c = m c := by
  apply write_outside
  · rw [toNat_wrap x k hk hw]; omega
  · rw [toNat_wrap x k hk hw]; omega

/-- The discharger for the lemmas above: rewrites the `toNat` of base-plus-offset addresses, then `omega`. -/
macro "base_omega" : tactic => `(tactic| first | (simp (disch := omega) only [RV.toNat_base] <;> omega) | omega)

end RV
