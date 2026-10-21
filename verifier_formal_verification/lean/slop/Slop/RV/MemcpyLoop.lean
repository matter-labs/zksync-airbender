import Slop.RV.MemcpyIter

/-! `memcpy`, aligned path: its 64-byte loop, by induction on the iterations left. -/

set_option linter.deprecated false

namespace RV
set_option maxHeartbeats 400000

/-- One iteration in terms of the whole block copy. -/
theorem memcpy_iter_blk (A d s : Word) (N : Word → BitVec 8) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hd4 : d.toNat % 4 = 0) (hs4 : s.toNat % 4 = 0) (n : Nat) (hd : 4194304 ≤ d.toNat)
    (hdn : d.toNat + n ≤ 1073741824) (hsn : s.toNat + n ≤ 1073741824)
    (hdisj : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat) (S : State) (k : Nat) (hk4 : k % 4 = 0) (hk : k + 64 ≤ n)
    (hc : CodeAt S A Code.memcpy) (hpc : S.pc = A + 88#32) (h11 : S.getReg 11#5 = s + BitVec.ofNat 32 k)
    (h13 : S.getReg 13#5 = d + BitVec.ofNat 32 k) (h12 : S.getReg 12#5 = BitVec.ofNat 32 (n - k))
    (hm : S.mem = blockCopy N d s k) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 228#32 ∧ S'.getReg 11#5 = s + BitVec.ofNat 32 (k + 64) ∧
      S'.getReg 13#5 = d + BitVec.ofNat 32 (k + 64) ∧ S'.getReg 12#5 = BitVec.ofNat 32 (n - (k + 64)) ∧
      S'.mem = blockCopy N d s (k + 64) ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 15#5 → i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → S'.getReg i = S.getReg i) := by
  obtain ⟨m, S1, hrun, hpc1, h11', h13', h12', hm1, hreg⟩ := memcpy_iter A S _ _ _ hA hAr hc hpc h11 h13 h12
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
  have hm2 : S1.mem = blockCopy N d s (k + 64) := by
    rw [hm1, hm, blockCopy_append N d s k 64 (by omega) (by omega) (by omega)]
  refine ⟨m, S1, hrun, hpc1, ?_, ?_, ?_, hm2, ?_, hreg⟩
  · rw [h11']; bv_omega
  · rw [h13']; bv_omega
  · rw [h12']; bv_omega
  · exact codeAt_blockCopy hc hm1 (by simp only [ROM_END, memcpy_length]; omega)
      (by simp only [ROM_END]; bv_omega) (by bv_omega)

/-- `memcpy`'s 64-byte loop, from its head (`memcpy + 0x58`) with `r` bytes left (`64 ≤ r`, `t + 1 = r / 64`
iterations) until it leaves for the tail (`memcpy + 0x790`): copies `64 (t + 1)` more bytes of the block copy
`N, d, s`, `k` bytes of which are done. -/
theorem memcpy_loop (A d s : Word) (N : Word → BitVec 8) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hd4 : d.toNat % 4 = 0) (hs4 : s.toNat % 4 = 0) (n : Nat) (hd : 4194304 ≤ d.toNat)
    (hdn : d.toNat + n ≤ 1073741824) (hsn : s.toNat + n ≤ 1073741824)
    (hdisj : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat) (t : Nat) :
    ∀ (S : State) (k : Nat), k % 4 = 0 → (n - k) / 64 = t + 1 → k ≤ n →
    CodeAt S A Code.memcpy → S.pc = A + 88#32 → S.getReg 11#5 = s + BitVec.ofNat 32 k →
    S.getReg 13#5 = d + BitVec.ofNat 32 k → S.getReg 12#5 = BitVec.ofNat 32 (n - k) → S.getReg 14#5 = 63#32 →
    S.mem = blockCopy N d s k →
    ∃ m S', run m S = some S' ∧ S'.pc = A + 1936#32 ∧ S'.getReg 11#5 = s + BitVec.ofNat 32 (k + 64 * (t + 1)) ∧
      S'.getReg 13#5 = d + BitVec.ofNat 32 (k + 64 * (t + 1)) ∧ S'.getReg 12#5 = BitVec.ofNat 32 ((n - k) % 64) ∧
      S'.mem = blockCopy N d s (k + 64 * (t + 1)) ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 15#5 → i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → S'.getReg i = S.getReg i) := by
  induction t with
  | zero =>
    intro S k hk4 ht hkn hc hpc h11 h13 h12 h14 hm
    obtain ⟨m, S1, hrun, hpc1, h11', h13', h12', hm1, hc1, hreg⟩ := memcpy_iter_blk A d s N hA hAr hd4 hs4 n hd hdn hsn
      hdisj S k hk4 (by omega) hc hpc h11 h13 h12 hm
    apply run_of_run S S1 m _ hrun
    have h14' : S1.getReg 14#5 = 63#32 := by rw [hreg _ (by decide) (by decide) (by decide) (by decide), h14]
    have hlt : (n - (k + 64)) < 64 := by omega
    rv_code_facts_range hc1 Code.memcpy 57 59
    have hb : Cond.holds Cond.ltu (S1.getReg 14#5) (S1.getReg 12#5) = false := by
      rw [h14', h12']
      simp only [Cond.holds, BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
      rw [Nat.mod_eq_of_lt (show n - (k + 64) < 2 ^ 32 by omega)]
      omega
    rv_steps 2 with hpc1
    rv_ret
    have e : n - (k + 64) = (n - k) % 64 := by omega
    refine ⟨by rv_regs, by rv_regs; rw [h11'], by rv_regs; rw [h13'], by rv_regs; rw [h12', e], ?_,
      codeAt_set _ _ _ _ _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ hc1)), ?_⟩
    · simp only [rv_state, hm1]
    · intro i h15 h11 h12 h13
      by_cases h0 : i = 0#5
      · subst h0; simp only [r_set, ite_true]; exact (r_zero S).symm
      · simp only [r_set, h0, ite_false, jump_r, next_r]
        rw [if_neg (show ¬ i = 0 from h0)]
        exact hreg i h15 h11 h12 h13
  | succ t ih =>
    intro S k hk4 ht hkn hc hpc h11 h13 h12 h14 hm
    obtain ⟨m, S1, hrun, hpc1, h11', h13', h12', hm1, hc1, hreg⟩ := memcpy_iter_blk A d s N hA hAr hd4 hs4 n hd hdn hsn
      hdisj S k hk4 (by omega) hc hpc h11 h13 h12 hm
    apply run_of_run S S1 m _ hrun
    have h14' : S1.getReg 14#5 = 63#32 := by rw [hreg _ (by decide) (by decide) (by decide) (by decide), h14]
    rv_code_facts_range hc1 Code.memcpy 57 58
    have hb : Cond.holds Cond.ltu (S1.getReg 14#5) (S1.getReg 12#5) = true := by
      rw [h14', h12']
      simp only [Cond.holds, BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
      rw [Nat.mod_eq_of_lt (show n - (k + 64) < 2 ^ 32 by omega)]
      omega
    rv_steps 1 with hpc1
    obtain ⟨m2, S2, hrun2, hpc2, h112, h132, h122, hm2, hc2, hreg2⟩ := ih (S1.setPC (A + 88#32)) (k + 64) (by omega)
      (by omega) (by omega) (codeAt_jump _ _ _ _ hc1) (by rv_regs) (by rv_regs; rw [h11'])
      (by rv_regs; rw [h13']) (by rv_regs; rw [h12']) (by rv_regs; rw [h14']) (by rw [jump_mem, hm1])
    refine ⟨m2, S2, hrun2, hpc2, ?_, ?_, ?_, ?_, hc2, ?_⟩
    · rw [h112, show k + 64 + 64 * (t + 1) = k + 64 * (t + 1 + 1) by omega]
    · rw [h132, show k + 64 + 64 * (t + 1) = k + 64 * (t + 1 + 1) by omega]
    · rw [h122, show (n - (k + 64)) % 64 = (n - k) % 64 by omega]
    · rw [hm2, show k + 64 + 64 * (t + 1) = k + 64 * (t + 1 + 1) by omega]
    · intro i h15 h11 h12 h13
      rw [hreg2 i h15 h11 h12 h13, jump_r, hreg i h15 h11 h12 h13]
end RV
