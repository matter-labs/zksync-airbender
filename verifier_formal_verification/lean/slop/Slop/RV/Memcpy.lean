import Slop.RV.MemcpyTail

/-! `memcpy`, aligned path, whole: entry (prologue, alignment check, short/long dispatch), the 64-byte loop
(`MemcpyLoop`), the tail (`MemcpyTail`) and the epilogue. -/

set_option linter.deprecated false

namespace RV
set_option maxHeartbeats 0

theorem or_and3_of_aligned (s d : Word) (hs : s.toNat % 4 = 0) (hd : d.toNat % 4 = 0) : (s ||| d) &&& 3#32 = 0#32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_or, show (3#32).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.or_mod_two_pow, show (2 : Nat) ^ 2 = 4 from rfl, hs, hd]
  rfl


/-- `memcpy`'s tail from its start (`memcpy + 0x790`): `R < 64` bytes left, `c` done; ends at an epilogue with the
whole block copied. -/
theorem memcpy_tail32 (A d s : Word) (N : Word → BitVec 8) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hd4 : d.toNat % 4 = 0) (hs4 : s.toNat % 4 = 0)
    (n c R : Nat) (hd : 4194304 ≤ d.toNat) (hdn : d.toNat + n ≤ 1073741824) (hsn : s.toNat + n ≤ 1073741824)
    (hdisj : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat) (hR : R < 64) (hc4 : c % 4 = 0) (hcn : c + R ≤ n)
    (S : State) (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 1936#32)
    (h11 : S.getReg 11#5 = s + BitVec.ofNat 32 c) (h13 : S.getReg 13#5 = d + BitVec.ofNat 32 c)
    (h12 : S.getReg 12#5 = BitVec.ofNat 32 R) (hm : S.mem = blockCopy N d s c) :
    ∃ m S', run m S = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧ S'.mem = blockCopy N d s (c + R) ∧
      CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
  have hRt : (BitVec.ofNat 32 R).toNat = R := by rw [BitVec.toNat_ofNat]; omega
  rv_code_facts_range hcode Code.memcpy 484 486
  by_cases hbig : 32 ≤ R
  · have hb : Cond.holds Cond.geu (BitVec.ofNat 32 R) 32#32 = true := by
      simp only [Cond.holds, BitVec.ult, hRt, Bool.not_eq_true', decide_eq_false_iff_not]; simp; omega
    rv_steps 1 with hpc
    rv_branch_taken with hpc, h12, hb
    rv_name T hT
    refine run_cont (memcpy_blk32 A T (d + BitVec.ofNat 32 c) (s + BitVec.ofNat 32 c) hA hAr
      (by rw [← hT]; exact codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode)))
      (by rw [← hT]; rv_regs; rw [hpc]; bv_omega) (by rw [← hT]; rv_regs; exact h11) (by rw [← hT]; rv_regs; exact h13)
      ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]; omega
    · intro S1 ⟨hpc1, h111, h131, hm1, hc1, hreg1⟩
      refine run_cont (memcpy_tail16 A d s N hA hAr hd4 hs4 n (c + 32) R hd hdn hsn hdisj hR (by omega) (by omega) S1 hc1
        (Or.inr hpc1) (by rw [h111]; bv_omega) (by rw [h131]; bv_omega)
        (by rw [hreg1 _ (by decide) (by decide) (by decide), ← hT]; rv_regs; exact h12)
        (by rw [hm1, ← hT]; simp only [jump_mem, next_mem, set_mem]; rw [hm, blockCopy_append N d s c 32 (by omega) (by omega) (by omega)])) ?_
      intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
      refine ⟨0, S2, rfl, hpc2, by rw [hm2, show c + 32 + R % 32 = c + R by omega], hc2, ?_⟩
      intro i h11 h12 h13 h14
      rw [hreg2 i h11 h12 h13 h14, hreg1 i h14 h11 h13, ← hT, jump_r, next_r, r_set, if_neg h14, getReg_ite_zero]
  · have hb : Cond.holds Cond.geu (BitVec.ofNat 32 R) 32#32 = false := by
      simp only [Cond.holds, BitVec.ult, hRt, Bool.not_eq_false', decide_eq_true_eq]; simp; omega
    rv_steps 1 with hpc
    rv_branch_not_taken with hpc, h12, hb
    rv_name T hT
    refine run_cont (memcpy_tail16 A d s N hA hAr hd4 hs4 n c R hd hdn hsn hdisj hR hc4 (by omega) T
      (by rw [← hT]; exact codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode)))
      (Or.inl (by rw [← hT]; rv_regs; rw [hpc]; bv_omega))
      (by rw [← hT]; rv_regs; exact h11) (by rw [← hT]; rv_regs; exact h13) (by rw [← hT]; rv_regs; exact h12)
      (by rw [← hT]; simp only [next_mem, set_mem, hm])) ?_
    intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
    refine ⟨0, S2, rfl, hpc2, by rw [hm2, show R % 32 = R by omega], hc2, ?_⟩
    intro i h11 h12 h13 h14
    rw [hreg2 i h11 h12 h13 h14, ← hT, next_r, next_r, r_set, if_neg h14, getReg_ite_zero]


/-- `memcpy`'s epilogue (either copy: `+0x7c0` or `+0x8a8`): restores `ra`, `s0`, `sp` and returns. -/
theorem memcpy_epi (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304) (S : State)
    (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 1984#32 ∨ S.pc = A + 2216#32) (sp0 ra0 s00 : Word)
    (h2 : S.getReg 2#5 = sp0 + 4294967280#32) (hra : read S.mem (sp0 + 4294967292#32) 4 = ra0)
    (hs0 : read S.mem (sp0 + 4294967288#32) 4 = s00) (hsp : sp0.toNat % 16 = 0) (hsp1 : 4194304 + 16 ≤ sp0.toNat)
    (hsp2 : sp0.toNat ≤ 1073741824) (hra4 : ra0.toNat % 4 = 0) :
    ∃ m S', run m S = some S' ∧ S'.pc = ra0 ∧ S'.mem = S.mem ∧ S'.getReg 2#5 = sp0 ∧ S'.getReg 8#5 = s00 ∧
      S'.getReg 1#5 = ra0 ∧ (∀ i : Reg, i ≠ 1#5 → i ≠ 2#5 → i ≠ 8#5 → S'.getReg i = S.getReg i) := by
  rcases hpc with hpc | hpc
  · rv_code_facts_range hcode Code.memcpy 496 500
    rv_steps 4 with hpc, h2, hra, hs0
    rv_ret
    refine ⟨by rv_regs, by simp only [rv_state], by rv_regs, by rv_regs, by rv_regs, ?_⟩
    intro i h1 h2 h8
    by_cases h0 : i = 0#5
    · subst h0; rw [r_zero5, r_zero5]
    · simp only [jump_r, next_r, r_set, h0, h1, h2, h8, ite_false, show ¬ (i = 0) from h0]
  · rv_code_facts_range hcode Code.memcpy 554 558
    rv_steps 4 with hpc, h2, hra, hs0
    rv_ret
    refine ⟨by rv_regs, by simp only [rv_state], by rv_regs, by rv_regs, by rv_regs, ?_⟩
    intro i h1 h2 h8
    by_cases h0 : i = 0#5
    · subst h0; rw [r_zero5, r_zero5]
    · simp only [jump_r, next_r, r_set, h0, h1, h2, h8, ite_false, show ¬ (i = 0) from h0]


/-- The end of `memcpy`: from an epilogue, with the copy done into the memory `T.mem` after the prologue. -/
theorem memcpy_finish (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304) (S T S1 : State)
    (d s : Word) (n : Nat) (hd : 4194304 ≤ d.toNat) (hdn : d.toNat + n ≤ 1073741824)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 16 ≤ (S.getReg 2#5).toNat)
    (hsp2 : (S.getReg 2#5).toNat ≤ 1073741824) (hra : (S.getReg 1#5).toNat % 4 = 0)
    (hfd : d.toNat + n + 16 ≤ (S.getReg 2#5).toNat ∨ (S.getReg 2#5).toNat ≤ d.toNat)
    (hTm : T.mem = write (write S.mem (S.getReg 2#5 + 4294967292#32) (S.getReg 1#5) 4)
      (S.getReg 2#5 + 4294967288#32) (S.getReg 8#5) 4) (hT2 : T.getReg 2#5 = S.getReg 2#5 + 4294967280#32)
    (hTr : ∀ i : Reg, i ≠ 2#5 → i ≠ 8#5 → i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → i ≠ 15#5 →
      T.getReg i = S.getReg i)
    (hc1 : CodeAt S1 A Code.memcpy) (hpc1 : S1.pc = A + 1984#32 ∨ S1.pc = A + 2216#32)
    (hm1 : S1.mem = blockCopy T.mem d s n)
    (hreg1 : ∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → i ≠ 15#5 → S1.getReg i = T.getReg i) :
    ∃ m S', run m S1 = some S' ∧ S'.pc = S.getReg 1#5 ∧
      S'.mem = blockCopy (write (write S.mem (S.getReg 2#5 + 4294967292#32) (S.getReg 1#5) 4)
        (S.getReg 2#5 + 4294967288#32) (S.getReg 8#5) 4) d s n ∧
      S'.getReg 2#5 = S.getReg 2#5 ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → i ≠ 15#5 → S'.getReg i = S.getReg i) := by
  have h21 : S1.getReg 2#5 = S.getReg 2#5 + 4294967280#32 := by
    rw [hreg1 _ (by decide) (by decide) (by decide) (by decide) (by decide), hT2]
  have hra1 : read S1.mem (S.getReg 2#5 + 4294967292#32) 4 = S.getReg 1#5 := by
    rw [hm1, read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), hTm,
      read_write_disjoint _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), read_write_same4]
  have hs01 : read S1.mem (S.getReg 2#5 + 4294967288#32) 4 = S.getReg 8#5 := by
    rw [hm1, read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), hTm, read_write_same4]
  refine run_cont (memcpy_epi A hA hAr S1 hc1 hpc1 (S.getReg 2#5) (S.getReg 1#5) (S.getReg 8#5) h21 hra1 hs01
    hsp hsp1 hsp2 hra) ?_
  intro S2 ⟨hpc2, hm2, h22, h82, h12', hreg2⟩
  refine ⟨0, S2, rfl, hpc2, by rw [hm2, hm1, hTm], h22, fun i hi => by rw [hm2]; exact hc1 i hi, ?_⟩
  intro i h11 h12 h13 h14 h15
  by_cases h1 : i = 1#5
  · subst h1; exact h12'
  by_cases h2 : i = 2#5
  · subst h2; exact h22
  by_cases h8 : i = 8#5
  · subst h8; exact h82
  rw [hreg2 i h1 h2 h8, hreg1 i h11 h12 h13 h14 h15, hTr i h2 h8 h11 h12 h13 h14 h15]

/-- `memcpy` (riscv_common's, as in the real Airbender guests) on 4-aligned, disjoint ranges, any length `n`: returns
to `ra` with `n` bytes copied from `s` to `d` in the memory after its prologue (which saves `ra` and `s0` just below
`sp`); `sp` and the other registers outside `a1 … a5` restored or unchanged. -/
theorem memcpy_aligned (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304) (S : State)
    (d s : Word) (n : Nat) (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A)
    (h10 : S.getReg 10#5 = d) (h11 : S.getReg 11#5 = s) (h12 : S.getReg 12#5 = BitVec.ofNat 32 n)
    (hd4 : d.toNat % 4 = 0) (hs4 : s.toNat % 4 = 0) (hd : 4194304 ≤ d.toNat) (hdn : d.toNat + n ≤ 1073741824)
    (hsn : s.toNat + n ≤ 1073741824) (hdisj : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 16 ≤ (S.getReg 2#5).toNat)
    (hsp2 : (S.getReg 2#5).toNat ≤ 1073741824) (hra : (S.getReg 1#5).toNat % 4 = 0)
    (hfd : d.toNat + n + 16 ≤ (S.getReg 2#5).toNat ∨ (S.getReg 2#5).toNat ≤ d.toNat)
    (hfs : s.toNat + n + 16 ≤ (S.getReg 2#5).toNat ∨ (S.getReg 2#5).toNat ≤ s.toNat) :
    ∃ m S', run m S = some S' ∧ S'.pc = S.getReg 1#5 ∧
      S'.mem = blockCopy (write (write S.mem (S.getReg 2#5 + 4294967292#32) (S.getReg 1#5) 4)
        (S.getReg 2#5 + 4294967288#32) (S.getReg 8#5) 4) d s n ∧
      S'.getReg 2#5 = S.getReg 2#5 ∧ CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → i ≠ 15#5 → S'.getReg i = S.getReg i) := by
  have hor := or_and3_of_aligned s d hs4 hd4
  rv_code_facts_range hcode Code.memcpy 0 7
  rv_steps 6 with hpc, h10, h11, hor
  rv_branch_taken with hpc
  rv_code_facts_range hcode Code.memcpy 18 20
  rv_steps 1 with hpc
  have hnt : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  by_cases hsmall : n < 64
  · have hb : Cond.holds Cond.ltu (BitVec.ofNat 32 n) 64#32 = true := by
      simp only [Cond.holds, BitVec.ult, hnt]; simp; omega
    rv_branch_taken with hpc, h12, hb
    rv_code_facts_range hcode Code.memcpy 93 95
    rv_steps 2 with hpc, h10
    rv_name T hT
    refine run_cont (memcpy_tail32 A d s T.mem hA hAr hd4 hs4 n 0 n hd hdn hsn hdisj hsmall (by omega) (by omega) T
      ?_ (by rw [← hT]; rv_regs) (by rw [← hT]; rv_regs; (try rw [h11]); bv_omega)
      (by rw [← hT]; rv_regs; (try rw [h10]); bv_omega) (by rw [← hT]; rv_regs; exact h12) (blockCopy_zero _ _ _).symm) ?_
    · rw [← hT]; intro i hi
      rw [memcpy_length] at hi
      simp only [rv_state]
      rw [read_write_rom _ _ _ _ _ (by simp only [ROM_END]; bv_omega) (by simp only [writable, ROM_END, RAM_END]; bv_omega),
        read_write_rom _ _ _ _ _ (by simp only [ROM_END]; bv_omega) (by simp only [writable, ROM_END, RAM_END]; bv_omega)]
      exact hcode i (by rw [memcpy_length]; exact hi)
    · intro S1 ⟨hpc1, hm1, hc1, hreg1⟩
      refine memcpy_finish A hA hAr S T S1 d s n hd hdn hsp hsp1 hsp2 hra hfd
        (by rw [← hT]; simp only [rv_state]) (by rw [← hT]; rv_regs) ?_ hc1 hpc1 (by rw [hm1, Nat.zero_add])
        (fun i h11 h12 h13 h14 _ => hreg1 i h11 h12 h13 h14)
      intro i h2 h8 h11 h12 h13 h14 h15
      rw [← hT]
      by_cases h0 : i = 0#5
      · subst h0; rw [r_zero5, r_zero5]
      · simp only [rv_state, r_set, jump_r, next_r, h0, h2, h8, h13, ite_false, show ¬ (i = 0) from h0]
  · have hb : Cond.holds Cond.ltu (BitVec.ofNat 32 n) 64#32 = false := by
      simp only [Cond.holds, BitVec.ult, hnt]; simp; omega
    rv_branch_not_taken with hpc, h12, hb
    rv_code_facts_range hcode Code.memcpy 20 22
    rv_steps 2 with hpc, h10
    rv_name T hT
    have hTc : CodeAt T A Code.memcpy := by
      rw [← hT]; intro i hi
      rw [memcpy_length] at hi
      simp only [rv_state]
      rw [read_write_rom _ _ _ _ _ (by simp only [ROM_END]; bv_omega) (by simp only [writable, ROM_END, RAM_END]; bv_omega),
        read_write_rom _ _ _ _ _ (by simp only [ROM_END]; bv_omega) (by simp only [writable, ROM_END, RAM_END]; bv_omega)]
      exact hcode i (by rw [memcpy_length]; exact hi)
    refine run_cont (memcpy_loop A d s T.mem hA hAr hd4 hs4 n hd hdn hsn hdisj (n / 64 - 1) T 0 (by omega)
      (by omega) (by omega) hTc (by rw [← hT]; rv_regs) (by rw [← hT]; rv_regs; (try rw [h11]); bv_omega)
      (by rw [← hT]; rv_regs; (try rw [h10]); bv_omega) (by rw [← hT]; rv_regs; rw [h12, Nat.sub_zero])
      (by rw [← hT]; rv_regs) (blockCopy_zero _ _ _).symm) ?_
    intro S1 ⟨hpc1, h111, h131, h121, hm1, hc1, hreg1⟩
    refine run_cont (memcpy_tail32 A d s T.mem hA hAr hd4 hs4 n (0 + 64 * (n / 64 - 1 + 1)) ((n - 0) % 64) hd hdn hsn
      hdisj (by omega) (by omega) (by omega) S1 hc1 hpc1 h111 h131 h121 hm1) ?_
    intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
    refine memcpy_finish A hA hAr S T S2 d s n hd hdn hsp hsp1 hsp2 hra hfd
      (by rw [← hT]; simp only [rv_state]) (by rw [← hT]; rv_regs) ?_ hc2 hpc2
      (by rw [hm2, show 0 + 64 * (n / 64 - 1 + 1) + (n - 0) % 64 = n by omega])
      (fun i h11 h12 h13 h14 h15 => by rw [hreg2 i h11 h12 h13 h14, hreg1 i h15 h11 h12 h13])
    intro i h2 h8 h11 h12 h13 h14 h15
    rw [← hT]
    by_cases h0 : i = 0#5
    · subst h0; rw [r_zero5, r_zero5]
    · simp only [rv_state, r_set, jump_r, next_r, h0, h2, h8, h13, h14, ite_false, show ¬ (i = 0) from h0]

end RV
