module
public import Human.ISA.RV32

@[expose] public section

/-! Byte-memory lemmas for `RV.read` / `RV.write`. -/

namespace RV

theorem write_other (m : Word → BitVec 8) (a v : Word) (n : Nat) (b : Word)
    (h : ∀ i < n, b ≠ a + BitVec.ofNat 32 i) : write m a v n b = m b := by
  induction n generalizing m a v with
  | zero => rfl
  | succ n ih =>
    simp only [write]
    rw [ih]
    · have := h 0 (by omega)
      simp only [BitVec.add_zero] at this
      simp [this]
    · intro i hi e
      apply h (i + 1) (by omega)
      rw [e]; bv_omega

theorem read_congr (m m' : Word → BitVec 8) (a : Word) (k : Nat)
    (h : ∀ j < k, m (a + BitVec.ofNat 32 j) = m' (a + BitVec.ofNat 32 j)) : read m a k = read m' a k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih]
    intro j hj
    have := h (j + 1) (by omega)
    rwa [show a + 1 + BitVec.ofNat 32 j = a + BitVec.ofNat 32 (j + 1) by bv_omega]

/-- Reading `k` bytes at `c` is not affected by writing `n` bytes at `a` if the ranges are disjoint. -/
theorem read_write_disjoint (m : Word → BitVec 8) (a v c : Word) (n k : Nat)
    (h : a.toNat + n ≤ c.toNat ∨ c.toNat + k ≤ a.toNat) (ha : a.toNat + n ≤ 2 ^ 32) (hc : c.toNat + k ≤ 2 ^ 32) :
    read (write m a v n) c k = read m c k := by
  apply read_congr
  intro j hj
  apply write_other
  intro i hi
  bv_omega

theorem write_outside (m : Word → BitVec 8) (a v b : Word) (n : Nat)
    (h : b.toNat < a.toNat ∨ a.toNat + n ≤ b.toNat) (ha : a.toNat + n ≤ 2 ^ 32) : write m a v n b = m b := by
  apply write_other
  intro i hi
  bv_omega

/-- A word read at `b + c₂` through a word write at `b + c₁` (same base, constant offsets at least 4 apart modulo
2^32): the side condition is closed, so `decide` checks it. -/
theorem read_write_off (m : Word → BitVec 8) (b c1 c2 v : Word) (h : 4 ≤ (c2 - c1).toNat ∧ 4 ≤ (c1 - c2).toNat) :
    read (write m (b + c1) v 4) (b + c2) 4 = read m (b + c2) 4 := by
  apply read_congr; intro j hj; apply write_other; intro i hi; bv_omega

theorem read_write_off0l (m : Word → BitVec 8) (b c2 v : Word) (h : 4 ≤ c2.toNat ∧ 4 ≤ (0 - c2).toNat) :
    read (write m b v 4) (b + c2) 4 = read m (b + c2) 4 := by
  have := read_write_off m b 0 c2 v (by simpa using h); simpa using this

theorem read_write_off0r (m : Word → BitVec 8) (b c1 v : Word) (h : 4 ≤ (0 - c1).toNat ∧ 4 ≤ c1.toNat) :
    read (write m (b + c1) v 4) b 4 = read m b 4 := by
  have := read_write_off m b c1 0 v (by simpa using h); simpa using this

/-- `jalr` clears bit 0 of the target; on a 4-aligned target that changes nothing. -/
theorem and_not_one_of_aligned (x : Word) (h : x.toNat % 4 = 0) : x &&& ~~~1#32 = x := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_one]
  by_cases h0 : i = 0
  · subst h0
    simp only [BitVec.getElem_eq_testBit_toNat, Nat.testBit_zero]
    have : x.toNat % 2 = 0 := by omega
    simp [this]
  · simp [h0]

/-- Instruction fetch from ROM is not affected by stores (which go to RAM). -/
theorem read_write_rom (m : Word → BitVec 8) (a v c : Word) (n : Nat) (hc : c.toNat + 4 ≤ ROM_END)
    (ha : writable a n) : read (write m a v n) c 4 = read m c 4 := by
  simp only [writable, ROM_END, RAM_END] at hc ha
  exact read_write_disjoint m a v c n 4 (by omega) (by omega) (by omega)

theorem read_write_same4 (m : Word → BitVec 8) (a v : Word) : read (write m a v 4) a 4 = v := by
  simp only [read, write]
  have h1 : a + 1 ≠ a := by bv_omega
  have h2 : a + 1 + 1 ≠ a := by bv_omega
  have h3 : a + 1 + 1 + 1 ≠ a := by bv_omega
  have h4 : a + 1 + 1 ≠ a + 1 := by bv_omega
  have h5 : a + 1 + 1 + 1 ≠ a + 1 := by bv_omega
  have h6 : a + 1 + 1 + 1 ≠ a + 1 + 1 := by bv_omega
  simp only [h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, ite_true, ite_false]
  ext i hi
  simp [BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32)) with h | h | h | h
  · simp [h, BitVec.getLsbD_eq_getElem hi]
  · have e : 8 + (i - 8) = i := by omega
    simp [show ¬ i < 8 by omega, show i - 8 < 8 by omega, e, BitVec.getLsbD_eq_getElem hi]
  · have e : 16 + (i - 8 - 8) = i := by omega
    simp [show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show i - 8 - 8 < 8 by omega, e,
      BitVec.getLsbD_eq_getElem hi]
  · have e : 24 + (i - 8 - 8 - 8) = i := by omega
    simp [h, show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega,
      show i - 8 - 8 - 8 < 8 by omega, e]

/-! ROM image and RAM (`State.loadView`): a LOAD reads `rom` below `ROM_END`, `mem` from `ROM_END` on. -/

/-- One byte of `write m a v n` depends on `m` only at that byte. -/
theorem write_congr_at (m m' : Word → BitVec 8) (a v : Word) (n : Nat) (b : Word) (h : m b = m' b) :
    write m a v n b = write m' a v n b := by
  induction n generalizing m m' a v with
  | zero => exact h
  | succ n ih =>
    simp only [write]
    apply ih
    split <;> simp_all

/-- `loadView` as a function (for rewriting under a partial application). -/
theorem loadView_fun (s : State) : s.loadView = fun a => if a.toNat < ROM_END then s.rom a else s.mem a := by rfl

theorem loadView_low (s : State) (a : Word) (h : a.toNat < ROM_END) : s.loadView a = s.rom a := by
  simp [State.loadView, h]

theorem loadView_high (s : State) (a : Word) (h : ROM_END ≤ a.toNat) : s.loadView a = s.mem a := by
  simp [State.loadView, Nat.not_lt.mpr h]

/-- A read inside ROM through `loadView` reads the ROM image. -/
theorem read_loadView_rom (s : State) (a : Word) (n : Nat) (h : a.toNat + n ≤ ROM_END) :
    read s.loadView a n = read s.rom a n := by
  apply read_congr
  intro j hj
  apply loadView_low
  simp only [ROM_END] at h ⊢
  bv_omega

/-- A read inside RAM (from `ROM_END` on) through `loadView` reads RAM. -/
theorem read_loadView_ram (s : State) (a : Word) (n : Nat) (lo : ROM_END ≤ a.toNat) (hi : a.toNat + n ≤ 2 ^ 32) :
    read s.loadView a n = read s.mem a n := by
  apply read_congr
  intro j hj
  apply loadView_high
  simp only [ROM_END] at lo ⊢
  bv_omega

/-- A store from `ROM_END` on is a write to what LOADs see. -/
theorem loadView_store (s : State) (a v : Word) (n : Nat) (lo : ROM_END ≤ a.toNat) (hi : a.toNat + n ≤ 2 ^ 32) :
    (s.store a v n).loadView = write s.loadView a v n := by
  funext b
  by_cases hb : b.toNat < ROM_END
  · rw [loadView_low _ _ hb, write_outside _ _ _ _ _ (by omega) hi, loadView_low _ _ hb]
    rfl
  · rw [loadView_high _ _ (by omega)]
    exact write_congr_at _ _ _ _ _ _ (loadView_high _ _ (by omega)).symm

end RV
