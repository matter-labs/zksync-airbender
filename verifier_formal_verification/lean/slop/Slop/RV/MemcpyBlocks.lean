import Slop.RV.MemcpyLoop

/-! `memcpy`, aligned path: the tail blocks (32, 16, 8, 4, 2, 1 bytes) after the 64-byte loop, each copying from `q`
(`a1`) to `p` (`a3`) and advancing both. General in the code's address, the pointers and the memory. -/

set_option linter.deprecated false

namespace RV
set_option maxHeartbeats 400000

/-- The 32-byte block of `memcpy`'s tail (`memcpy + 0x7d0`). -/
theorem memcpy_blk32 (A : Word) (S : State) (p q : Word)
    (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 2000#32) (h11 : S.getReg 11#5 = q) (h13 : S.getReg 13#5 = p)
    (hp : 4194304 ≤ p.toNat) (hp2 : p.toNat + 32 ≤ 1073741824) (hp4 : p.toNat % 4 = 0) (hq4 : q.toNat % 4 = 0)
    (hq : q.toNat + 32 ≤ 1073741824) (hdisj : q.toNat + 32 ≤ p.toNat ∨ p.toNat + 32 ≤ q.toNat) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 2072#32 ∧ S'.getReg 11#5 = q + 32#32 ∧ S'.getReg 13#5 = p + 32#32 ∧
      S'.mem = blockCopy S.mem p q 32 ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 14#5 → i ≠ 11#5 → i ≠ 13#5 → S'.getReg i = S.getReg i) := by
  rv_code_facts_range hcode Code.memcpy 500 514
  obtain ⟨S1, hrun1, hpc1, hm1, hreg1⟩ := run_copy_pairs 14#5 11#5 13#5 (by decide) (by decide) (by decide) (by decide)
    (by decide) S.mem p q 7 S (A + 2000#32) 0 hpc (by bv_omega) (by simp only [ROM_END]; bv_omega)
    (by intro i hi; nat_cases i hi <;> simp only [rv_word, rv_state, Nat.reduceMul, Nat.reduceAdd, BitVec.reduceAdd,
      and_self, *])
    h11 h13 (blockCopy_zero _ _ _).symm hp4 hq4 (by omega) (by simp only [ROM_END]; omega)
    (by simp only [RAM_END]; omega) (by simp only [RAM_END]; omega) (by omega)
  apply run_of_run S S1 _ _ hrun1
  have hc1 : CodeAt S1 A Code.memcpy := codeAt_blockCopy hcode hm1 (by simp only [ROM_END, memcpy_length]; omega)
    (by simp only [ROM_END]; omega) (by simp only [Nat.reducePow]; omega)
  rv_clear_facts
  have h11' : S1.getReg 11#5 = q := by rw [hreg1 _ (by decide), h11]
  have h13' : S1.getReg 13#5 = p := by rw [hreg1 _ (by decide), h13]
  simp only [Nat.reduceMul, Nat.zero_add, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hpc1 hm1
  rv_code_facts_range hc1 Code.memcpy 514 518
  rv_steps 4 with hpc1, h11', h13'
  rv_ret
  refine ⟨by rv_regs; rw [hpc1]; bv_omega, by rv_regs, by rv_regs, ?_,
    codeAt_next _ _ _ (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_store _ _ _ _ _ _ (codeAt_next _ _ _
      (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hc1)))) (by simp only [ROM_END, memcpy_length]; omega)
      (by simp only [rv_state, writable, ROM_END, RAM_END]; bv_omega)))), ?_⟩
  · simp only [rv_state, h11', h13', hm1]
    rw [read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)]
    exact copy_step _ p q 28 4 (by omega) (by omega)
  · intro i h14 h11 h13
    by_cases h0 : i = 0#5
    · subst h0; simp only [next_r, store_r, r_set, ite_true]; exact (r_zero S).symm
    · simp only [next_r, store_r, r_set, h0, h14, h11, h13, ite_false]
      simp only [show ¬ (i = 0) from h0, ite_false]
      exact hreg1 i h14

/-- The 16-byte block of `memcpy`'s tail (`memcpy + 0x820`). -/
theorem memcpy_blk16 (A : Word) (S : State) (p q : Word)
    (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 2080#32) (h11 : S.getReg 11#5 = q) (h13 : S.getReg 13#5 = p)
    (hp : 4194304 ≤ p.toNat) (hp2 : p.toNat + 16 ≤ 1073741824) (hp4 : p.toNat % 4 = 0) (hq4 : q.toNat % 4 = 0)
    (hq : q.toNat + 16 ≤ 1073741824) (hdisj : q.toNat + 16 ≤ p.toNat ∨ p.toNat + 16 ≤ q.toNat) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 2120#32 ∧ S'.getReg 11#5 = q + 16#32 ∧ S'.getReg 13#5 = p + 16#32 ∧
      S'.mem = blockCopy S.mem p q 16 ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 14#5 → i ≠ 11#5 → i ≠ 13#5 → S'.getReg i = S.getReg i) := by
  rv_code_facts_range hcode Code.memcpy 520 526
  obtain ⟨S1, hrun1, hpc1, hm1, hreg1⟩ := run_copy_pairs 14#5 11#5 13#5 (by decide) (by decide) (by decide) (by decide)
    (by decide) S.mem p q 3 S (A + 2080#32) 0 hpc (by bv_omega) (by simp only [ROM_END]; bv_omega)
    (by intro i hi; nat_cases i hi <;> simp only [rv_word, rv_state, Nat.reduceMul, Nat.reduceAdd, BitVec.reduceAdd,
      and_self, *])
    h11 h13 (blockCopy_zero _ _ _).symm hp4 hq4 (by omega) (by simp only [ROM_END]; omega)
    (by simp only [RAM_END]; omega) (by simp only [RAM_END]; omega) (by omega)
  apply run_of_run S S1 _ _ hrun1
  have hc1 : CodeAt S1 A Code.memcpy := codeAt_blockCopy hcode hm1 (by simp only [ROM_END, memcpy_length]; omega)
    (by simp only [ROM_END]; omega) (by simp only [Nat.reducePow]; omega)
  rv_clear_facts
  have h11' : S1.getReg 11#5 = q := by rw [hreg1 _ (by decide), h11]
  have h13' : S1.getReg 13#5 = p := by rw [hreg1 _ (by decide), h13]
  simp only [Nat.reduceMul, Nat.zero_add, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hpc1 hm1
  rv_code_facts_range hc1 Code.memcpy 526 530
  rv_steps 4 with hpc1, h11', h13'
  rv_ret
  refine ⟨by rv_regs; rw [hpc1]; bv_omega, by rv_regs, by rv_regs, ?_,
    codeAt_next _ _ _ (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_store _ _ _ _ _ _ (codeAt_next _ _ _
      (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hc1)))) (by simp only [ROM_END, memcpy_length]; omega)
      (by simp only [rv_state, writable, ROM_END, RAM_END]; bv_omega)))), ?_⟩
  · simp only [rv_state, h11', h13', hm1]
    rw [read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)]
    exact copy_step _ p q 12 4 (by omega) (by omega)
  · intro i h14 h11 h13
    by_cases h0 : i = 0#5
    · subst h0; simp only [next_r, store_r, r_set, ite_true]; exact (r_zero S).symm
    · simp only [next_r, store_r, r_set, h0, h14, h11, h13, ite_false]
      simp only [show ¬ (i = 0) from h0, ite_false]
      exact hreg1 i h14

/-- The 8-byte block of `memcpy`'s tail (`memcpy + 0x850`). -/
theorem memcpy_blk8 (A : Word) (S : State) (p q : Word)
    (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 2128#32) (h11 : S.getReg 11#5 = q) (h13 : S.getReg 13#5 = p)
    (hp : 4194304 ≤ p.toNat) (hp2 : p.toNat + 8 ≤ 1073741824) (hp4 : p.toNat % 4 = 0) (hq4 : q.toNat % 4 = 0)
    (hq : q.toNat + 8 ≤ 1073741824) (hdisj : q.toNat + 8 ≤ p.toNat ∨ p.toNat + 8 ≤ q.toNat) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 2152#32 ∧ S'.getReg 11#5 = q + 8#32 ∧ S'.getReg 13#5 = p + 8#32 ∧
      S'.mem = blockCopy S.mem p q 8 ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 14#5 → i ≠ 11#5 → i ≠ 13#5 → S'.getReg i = S.getReg i) := by
  rv_code_facts_range hcode Code.memcpy 532 534
  obtain ⟨S1, hrun1, hpc1, hm1, hreg1⟩ := run_copy_pairs 14#5 11#5 13#5 (by decide) (by decide) (by decide) (by decide)
    (by decide) S.mem p q 1 S (A + 2128#32) 0 hpc (by bv_omega) (by simp only [ROM_END]; bv_omega)
    (by intro i hi; nat_cases i hi <;> simp only [rv_word, rv_state, Nat.reduceMul, Nat.reduceAdd, BitVec.reduceAdd,
      and_self, *])
    h11 h13 (blockCopy_zero _ _ _).symm hp4 hq4 (by omega) (by simp only [ROM_END]; omega)
    (by simp only [RAM_END]; omega) (by simp only [RAM_END]; omega) (by omega)
  apply run_of_run S S1 _ _ hrun1
  have hc1 : CodeAt S1 A Code.memcpy := codeAt_blockCopy hcode hm1 (by simp only [ROM_END, memcpy_length]; omega)
    (by simp only [ROM_END]; omega) (by simp only [Nat.reducePow]; omega)
  rv_clear_facts
  have h11' : S1.getReg 11#5 = q := by rw [hreg1 _ (by decide), h11]
  have h13' : S1.getReg 13#5 = p := by rw [hreg1 _ (by decide), h13]
  simp only [Nat.reduceMul, Nat.zero_add, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hpc1 hm1
  rv_code_facts_range hc1 Code.memcpy 534 538
  rv_steps 4 with hpc1, h11', h13'
  rv_ret
  refine ⟨by rv_regs; rw [hpc1]; bv_omega, by rv_regs, by rv_regs, ?_,
    codeAt_next _ _ _ (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_store _ _ _ _ _ _ (codeAt_next _ _ _
      (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hc1)))) (by simp only [ROM_END, memcpy_length]; omega)
      (by simp only [rv_state, writable, ROM_END, RAM_END]; bv_omega)))), ?_⟩
  · simp only [rv_state, h11', h13', hm1]
    rw [read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)]
    exact copy_step _ p q 4 4 (by omega) (by omega)
  · intro i h14 h11 h13
    by_cases h0 : i = 0#5
    · subst h0; simp only [next_r, store_r, r_set, ite_true]; exact (r_zero S).symm
    · simp only [next_r, store_r, r_set, h0, h14, h11, h13, ite_false]
      simp only [show ¬ (i = 0) from h0, ite_false]
      exact hreg1 i h14

/-- The 4-byte block of `memcpy`'s tail (`memcpy + 0x870`). -/
theorem memcpy_blk4 (A : Word) (S : State) (p q : Word)
    (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 2160#32) (h11 : S.getReg 11#5 = q) (h13 : S.getReg 13#5 = p)
    (hp : 4194304 ≤ p.toNat) (hp2 : p.toNat + 4 ≤ 1073741824) (hp4 : p.toNat % 4 = 0) (hq4 : q.toNat % 4 = 0)
    (hq : q.toNat + 4 ≤ 1073741824) (hdisj : q.toNat + 4 ≤ p.toNat ∨ p.toNat + 4 ≤ q.toNat) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 2176#32 ∧ S'.getReg 11#5 = q + 4#32 ∧ S'.getReg 13#5 = p + 4#32 ∧
      S'.mem = blockCopy S.mem p q 4 ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 14#5 → i ≠ 11#5 → i ≠ 13#5 → S'.getReg i = S.getReg i) := by
  rv_code_facts_range hcode Code.memcpy 540 544
  rv_steps 4 with hpc, h11, h13
  rv_ret
  refine ⟨by rv_regs; rw [hpc]; bv_omega, by rv_regs, by rv_regs, ?_,
    codeAt_next _ _ _ (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_store _ _ _ _ _ _ (codeAt_next _ _ _
      (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode)))) (by simp only [ROM_END, memcpy_length]; omega)
      (by simp only [rv_state, writable, ROM_END, RAM_END]; bv_omega)))), ?_⟩
  · simp only [rv_state, h11, h13]
    exact copy_first _ p q 4 (by omega)
  · intro i h14 h11 h13
    by_cases h0 : i = 0#5
    · subst h0; simp only [next_r, store_r, r_set, ite_true]; exact (r_zero S).symm
    · simp only [next_r, store_r, r_set, h0, h14, h11, h13, ite_false, show ¬ (i = 0) from h0]

/-- The 2-byte block of `memcpy`'s tail (`memcpy + 0x888`): `lh` / `sh`. -/
theorem memcpy_blk2 (A : Word) (S : State) (p q : Word)
    (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 2184#32) (h11 : S.getReg 11#5 = q) (h13 : S.getReg 13#5 = p)
    (hp : 4194304 ≤ p.toNat) (hp2 : p.toNat + 2 ≤ 1073741824) (hp4 : p.toNat % 2 = 0) (hq4 : q.toNat % 2 = 0)
    (hq : q.toNat + 2 ≤ 1073741824) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 2200#32 ∧ S'.getReg 11#5 = q + 2#32 ∧ S'.getReg 13#5 = p + 2#32 ∧
      S'.mem = blockCopy S.mem p q 2 ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 14#5 → i ≠ 11#5 → i ≠ 13#5 → S'.getReg i = S.getReg i) := by
  rv_code_facts_range hcode Code.memcpy 546 550
  rv_steps 4 with hpc, h11, h13
  rv_ret
  refine ⟨by rv_regs; rw [hpc]; bv_omega, by rv_regs, by rv_regs, ?_,
    codeAt_next _ _ _ (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_store _ _ _ _ _ _ (codeAt_next _ _ _
      (codeAt_set _ _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode)))) (by simp only [ROM_END, memcpy_length]; omega)
      (by simp only [rv_state, writable, ROM_END, RAM_END]; bv_omega)))), ?_⟩
  · simp only [rv_state, h11, h13, ite_true]
    rw [write_signExtend2]
    exact copy_first _ p q 2 (by omega)
  · intro i h14 h11 h13
    by_cases h0 : i = 0#5
    · subst h0; simp only [next_r, store_r, r_set, ite_true]; exact (r_zero S).symm
    · simp only [next_r, store_r, r_set, h0, h14, h11, h13, ite_false, show ¬ (i = 0) from h0]

/-- The 1-byte block of `memcpy`'s tail (`memcpy + 0x8a0`): `lbu a1` / `sb`. -/
theorem memcpy_blk1 (A : Word) (S : State) (p q : Word)
    (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 2208#32) (h11 : S.getReg 11#5 = q) (h13 : S.getReg 13#5 = p)
    (hp : 4194304 ≤ p.toNat) (hp2 : p.toNat + 1 ≤ 1073741824) (hq : q.toNat + 1 ≤ 1073741824) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 2216#32 ∧ S'.getReg 13#5 = p ∧
      S'.mem = blockCopy S.mem p q 1 ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 11#5 → S'.getReg i = S.getReg i) := by
  rv_code_facts_range hcode Code.memcpy 552 554
  rv_steps 2 with hpc, h11, h13
  rv_ret
  refine ⟨by rv_regs; rw [hpc]; bv_omega, by rv_regs; exact h13, ?_,
    codeAt_next _ _ _ (codeAt_store _ _ _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))
      (by simp only [ROM_END, memcpy_length]; omega) (by simp only [rv_state, writable, ROM_END, RAM_END]; bv_omega)), ?_⟩
  · simp only [rv_state, h11, h13, ite_false]
    exact copy_first _ p q 1 (by omega)
  · intro i h11
    by_cases h0 : i = 0#5
    · subst h0; simp only [next_r, store_r, r_set, ite_true]; exact (r_zero S).symm
    · simp only [next_r, store_r, r_set, h0, h11, ite_false, show ¬ (i = 0) from h0]

/-! Goal-directed forms: continue from the state after the block. -/


end RV
