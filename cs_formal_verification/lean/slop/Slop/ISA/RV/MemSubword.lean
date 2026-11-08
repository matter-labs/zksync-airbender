module
public import Slop.ISA.RV.Mem

@[expose] public section

/-! Byte and halfword accesses inside an aligned memory word, for `RV.read` / `RV.write`: a 1- or 2-byte read at
    byte `k` of the word at `a` is a slice of the word read, and a 1- or 2-byte write there is the 4-byte write of the
    word with that slice replaced. -/

namespace RV

/-- `exec`'s extension of a loaded byte or halfword: sign extension for LB/LH, zero extension for LBU/LHU. -/
def extendLoad (signed : Bool) {n : Nat} (x : BitVec n) : Word :=
  if signed then x.signExtend 32 else x.setWidth 32

/-- Byte `j < n` of an `n`-byte write is byte `j` of the value. -/
theorem write_byte (m : Word → BitVec 8) (a v : Word) (n j : Nat) (hj : j < n) (hn : n ≤ 4) :
    write m a v n (a + BitVec.ofNat 32 j) = (v >>> (8 * j)).setWidth 8 := by
  induction n generalizing m a v j with
  | zero => omega
  | succ n ih =>
    simp only [write]
    cases j with
    | zero =>
      rw [write_other]
      · simp
      · intro i hi
        bv_omega
    | succ j =>
      have shift : a + BitVec.ofNat 32 (j + 1) = a + 1 + BitVec.ofNat 32 j := by bv_omega
      rw [shift, ih _ _ _ j (by omega) (by omega), ← BitVec.shiftRight_add]
      congr 2
      omega

/-- Byte `j < n` of an `n`-byte read is the memory byte at `a + j`. -/
theorem read_byte (m : Word → BitVec 8) (a : Word) (n j : Nat) (hj : j < n) (hn : n ≤ 4) :
    (read m a n >>> (8 * j)).setWidth 8 = m (a + BitVec.ofNat 32 j) := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
    simp only [read]
    cases j with
    | zero =>
      ext i hi
      simp
    | succ j =>
      have shift : a + BitVec.ofNat 32 (j + 1) = a + 1 + BitVec.ofNat 32 j := by bv_omega
      rw [shift, ← ih (a + 1) j (by omega) (by omega)]
      ext i hi
      have small : 8 * (j + 1) + i < 32 := by omega
      simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
        BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
      simp [show 8 * (j + 1) + i < 32 from small, show ¬ 8 * (j + 1) + i < 8 by omega,
        show 8 * (j + 1) + i - 8 = 8 * j + i by omega, BitVec.getLsbD_of_ge (m a) (8 * (j + 1) + i) (by omega)]

/-- A byte or halfword read at byte `k` of the word at `a` is that slice of the word, zero-extended. -/
theorem read_subword (m : Word → BitVec 8) (a : Word) (n k : Nat) (hn : n = 1 ∨ n = 2) (hk : k + n ≤ 4) :
    read m (a + BitVec.ofNat 32 k) n = ((read m a 4 >>> (8 * k)).setWidth (8 * n)).setWidth 32 := by
  have byte (j : Nat) (hj : k + j < 4) :
      m (a + BitVec.ofNat 32 k + BitVec.ofNat 32 j) = (read m a 4 >>> (8 * (k + j))).setWidth 8 := by
    rw [read_byte m a 4 (k + j) hj (by omega)]
    congr 1
    bv_omega
  rcases hn with rfl | rfl
  · have b0 := byte 0 (by omega)
    simp only [BitVec.add_zero, Nat.add_zero] at b0
    generalize read m a 4 = W at b0
    simp only [read, b0]
    ext i hi
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    by_cases low : i < 8 <;> simp [low]
  · have b0 := byte 0 (by omega)
    have b1 : m (a + BitVec.ofNat 32 k + 1) = (read m a 4 >>> (8 * (k + 1))).setWidth 8 := byte 1 (by omega)
    simp only [BitVec.add_zero, Nat.add_zero] at b0
    generalize read m a 4 = W at b0 b1
    simp only [read, b0, b1]
    ext i hi
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    by_cases low : i < 8
    · simp [low, show i < 16 by omega]
    · by_cases mid : i < 16
      · simp [low, mid, show i - 8 < 8 by omega, show 8 * (k + 1) + (i - 8) = 8 * k + i by omega]
      · simp [low, mid, show ¬ i - 8 < 8 by omega]

/-- A byte or halfword write at byte `k` of the word at `a` is the word write of `merged`, the old word read with
    bytes `k .. k + n - 1` replaced by the low bytes of `v`. -/
theorem write_subword (m : Word → BitVec 8) (a v merged : Word) (n k : Nat) (hk : k + n ≤ 4)
    (bytes : ∀ i : Fin 4, merged.extractLsb' (8 * i.val) 8 =
      if k ≤ i.val ∧ i.val < k + n then (v.setWidth (8 * n)).extractLsb' (8 * (i.val - k)) 8
      else (read m a 4).extractLsb' (8 * i.val) 8) :
    write m (a + BitVec.ofNat 32 k) v n = write m a merged 4 := by
  have extract {width : Nat} (x : BitVec width) (s : Nat) : x.extractLsb' s 8 = (x >>> s).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hn4 : n ≤ 4 := by omega
  funext b
  by_cases inside : ∃ j, j < 4 ∧ b = a + BitVec.ofNat 32 j
  · obtain ⟨j, hj, rfl⟩ := inside
    rw [write_byte m a merged 4 j hj (le_refl _), ← extract, bytes ⟨j, hj⟩]
    dsimp only
    by_cases window : k ≤ j ∧ j < k + n
    · simp only [window, and_self, ite_true]
      have shift : a + BitVec.ofNat 32 j = a + BitVec.ofNat 32 k + BitVec.ofNat 32 (j - k) := by bv_omega
      rw [shift, write_byte m _ v n (j - k) (by omega) hn4, extract]
      ext i hi
      simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
      simp [show 8 * (j - k) + i < 8 * n by omega]
    · simp only [window, ite_false]
      rw [write_other, extract, read_byte m a 4 j hj (le_refl _)]
      intro i hi equal
      apply window
      have : (a + BitVec.ofNat 32 j).toNat = (a + BitVec.ofNat 32 k + BitVec.ofNat 32 i).toNat := by rw [equal]
      bv_omega
  · rw [write_other, write_other]
    · intro i hi equal
      exact inside ⟨i, hi, equal⟩
    · intro i hi equal
      exact inside ⟨k + i, by omega, by rw [equal]; bv_omega⟩

/-- An LB/LBU/LH/LHU at byte `k` of the aligned word at `a` loads the extension of that word's slice. -/
theorem exec_load_subword (s : State) (n : Nat) (hn : n = 1 ∨ n = 2) (signed : Bool) (rd rs1 : Reg)
    (offset a : Word) (k : Nat) (hrd : rd ≠ 0) (addr : s.getReg rs1 + offset = a + BitVec.ofNat 32 k)
    (ha : a.toNat % 4 = 0) (hk : k + n ≤ 4) (hkn : k % n = 0) :
    exec s (.load n signed rd rs1 offset) =
      some ((s.setReg rd (extendLoad signed ((read s.loadView a 4 >>> (8 * k)).setWidth (8 * n)))).nextInstr) := by
  have small := a.isLt
  have sum : (a + BitVec.ofNat 32 k).toNat = a.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have guard : aligned (a + BitVec.ofNat 32 k) n ∧ readable (a + BitVec.ofNat 32 k) n := by
    simp only [aligned, readable, RAM_END, sum]
    rcases hn with rfl | rfl <;> omega
  simp only [exec, addr]
  rw [ite_eq_right hrd, ite_eq_left guard, read_subword s.loadView a n k hn hk]
  rcases hn with rfl | rfl <;> cases signed <;>
    simp [extendLoad, BitVec.setWidth_setWidth_of_le]

/-- An SB/SH at byte `k` of the aligned RAM word at `a` stores `merged`: the old word with that slice replaced by
    the low bytes of rs2. -/
theorem exec_store_subword (s : State) (n : Nat) (hn : n = 1 ∨ n = 2) (rs2 rs1 : Reg) (offset a merged : Word)
    (k : Nat) (addr : s.getReg rs1 + offset = a + BitVec.ofNat 32 k) (ha : a.toNat % 4 = 0)
    (rom : ROM_END ≤ a.toNat) (hk : k + n ≤ 4) (hkn : k % n = 0)
    (bytes : ∀ i : Fin 4, merged.extractLsb' (8 * i.val) 8 =
      if k ≤ i.val ∧ i.val < k + n then ((s.getReg rs2).setWidth (8 * n)).extractLsb' (8 * (i.val - k)) 8
      else (read s.mem a 4).extractLsb' (8 * i.val) 8) :
    exec s (.store n rs2 rs1 offset) = some (s.store a merged 4).nextInstr := by
  have small := a.isLt
  have sum : (a + BitVec.ofNat 32 k).toNat = a.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have guard : aligned (a + BitVec.ofNat 32 k) n ∧ writable (a + BitVec.ofNat 32 k) n := by
    simp only [aligned, writable, RAM_END, sum]
    rcases hn with rfl | rfl <;> omega
  simp only [exec, addr]
  rw [ite_eq_left guard]
  simp only [State.store, write_subword s.mem a (s.getReg rs2) merged n k hk bytes]

end RV
