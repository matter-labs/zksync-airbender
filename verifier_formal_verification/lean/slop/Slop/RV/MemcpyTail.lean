import Slop.RV.MemcpyBlocks

/-! `memcpy`, aligned path: the tail's decisions on the bits of the remaining count (`< 64`), from bit 4 (`16`) down
to bit 0, each running its block (`MemcpyBlocks`) when the bit is set; ends at one of the two epilogues. -/

set_option linter.deprecated false

namespace RV
set_option maxHeartbeats 0

theorem and_bit (R i : Nat) (hi : i < 32) :
    BitVec.ofNat 32 R &&& BitVec.ofNat 32 (2 ^ i) = if R / 2 ^ i % 2 = 1 then BitVec.ofNat 32 (2 ^ i) else 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow, hj, decide_true, Bool.true_and]
  split <;> rename_i h <;>
    simp only [BitVec.getLsbD_ofNat, Nat.testBit_two_pow, BitVec.getLsbD_zero, hj, decide_true, Bool.true_and] <;>
    by_cases hji : i = j <;> simp [hji, Nat.testBit_eq_decide_div_mod_eq] <;> subst hji <;> omega

theorem getReg_ite_zero (S : State) (i : Reg) : (if i = 0 then 0 else S.getReg i) = S.getReg i := by
  split
  · rename_i h; subst h; exact (r_zero S).symm
  · rfl

/-- The last decision of `memcpy`'s tail (bit 0 of the remaining count `R`, at `+0x7b8` or `+0x898`), then the
1-byte block if needed: ends at one of the two epilogues. -/
theorem memcpy_tail1 (A d s : Word) (N : Word → BitVec 8) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (n c R : Nat) (hd : 4194304 ≤ d.toNat) (hdn : d.toNat + n ≤ 1073741824) (hsn : s.toNat + n ≤ 1073741824)
    (hdisj : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat) (hR : R < 64) (hcn : c + R % 2 ≤ n)
    (S : State) (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 1976#32 ∨ S.pc = A + 2200#32)
    (h11 : S.getReg 11#5 = s + BitVec.ofNat 32 c) (h13 : S.getReg 13#5 = d + BitVec.ofNat 32 c)
    (h12 : S.getReg 12#5 = BitVec.ofNat 32 R) (hm : S.mem = blockCopy N d s c) :
    ∃ m S', run m S = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧ S'.mem = blockCopy N d s (c + R % 2) ∧
      CodeAt S' A Code.memcpy ∧ (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → S'.getReg i = S.getReg i) := by
  have hand := and_bit R 0 (by decide)
  simp only [Nat.pow_zero, Nat.div_one] at hand
  -- the 1-byte block, from a state at `+0x8a0` (only `a2` changed since `S`)
  have blk : ∀ T : State, CodeAt T A Code.memcpy → T.pc = A + 2208#32 → T.mem = S.mem →
      (∀ i : Reg, i ≠ 12#5 → T.getReg i = S.getReg i) → R % 2 = 1 →
      ∃ m S', run m T = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧
        S'.mem = blockCopy N d s (c + R % 2) ∧ CodeAt S' A Code.memcpy ∧
        (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → S'.getReg i = S.getReg i) := by
    intro T hcT hpcT hmT hregT hbit
    refine run_cont (memcpy_blk1 A T (d + BitVec.ofNat 32 c) (s + BitVec.ofNat 32 c) hA hAr hcT hpcT
      (by rw [hregT _ (by decide), h11]) (by rw [hregT _ (by decide), h13]) ?_ ?_ ?_) ?_
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · intro S' ⟨hpc', h13', hm', hc', hreg'⟩
      refine ⟨0, S', rfl, Or.inr hpc', ?_, hc', ?_⟩
      · rw [hm', hmT, hm, hbit, blockCopy_append N d s c 1 (by omega) (by omega) (by omega)]
      · intro i h11 h12; rw [hreg' i h11, hregT i h12]
  by_cases hbit : R % 2 = 1
  · rw [if_pos hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 494 496
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs)
        (by simp only [jump_mem, next_mem, set_mem])
        (fun i hi => by rw [jump_r, next_r, r_set, if_neg hi, getReg_ite_zero]) hbit
    · rv_code_facts_range hcode Code.memcpy 550 552
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [next_mem, set_mem])
        (fun i hi => by rw [next_r, next_r, r_set, if_neg hi, getReg_ite_zero]) hbit
  · have h0 : R % 2 = 0 := by omega
    rw [if_neg hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 494 496
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      rv_ret
      refine ⟨Or.inl (by rv_regs; rw [hpc]; bv_omega), by rw [h0, Nat.add_zero]; simp only [rv_state, hm],
        codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode)), ?_⟩
      intro i h11 h12; rw [next_r, next_r, r_set, if_neg h12, getReg_ite_zero]
    · rv_code_facts_range hcode Code.memcpy 550 552
      rv_steps 1 with hpc, h12, hand
      rv_branch_taken with hpc
      rv_ret
      refine ⟨Or.inl (by rv_regs; rw [hpc]; bv_omega), by rw [h0, Nat.add_zero]; simp only [rv_state, hm],
        codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode)), ?_⟩
      intro i h11 h12; rw [jump_r, next_r, r_set, if_neg h12, getReg_ite_zero]

/-- Decision on bit 1 (`2`) of the remaining count `R` (at `+0x7b0` or `+0x880`), then the 2-byte block if
needed, then the lower bits. -/
theorem memcpy_tail2 (A d s : Word) (N : Word → BitVec 8) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hd4 : d.toNat % 4 = 0) (hs4 : s.toNat % 4 = 0)
    (n c R : Nat) (hd : 4194304 ≤ d.toNat) (hdn : d.toNat + n ≤ 1073741824) (hsn : s.toNat + n ≤ 1073741824)
    (hdisj : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat) (hR : R < 64) (hc4 : c % 4 = 0) (hcn : c + R % 4 ≤ n)
    (S : State) (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 1968#32 ∨ S.pc = A + 2176#32)
    (h11 : S.getReg 11#5 = s + BitVec.ofNat 32 c) (h13 : S.getReg 13#5 = d + BitVec.ofNat 32 c)
    (h12 : S.getReg 12#5 = BitVec.ofNat 32 R) (hm : S.mem = blockCopy N d s c) :
    ∃ m S', run m S = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧ S'.mem = blockCopy N d s (c + R % 4) ∧
      CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
  have hand := and_bit R 1 (by decide)
  simp only [Nat.reducePow] at hand
  -- the 2-byte block (from `+0x888`), then the lower bits
  have blk : ∀ T : State, CodeAt T A Code.memcpy → T.pc = A + 2184#32 → T.mem = S.mem →
      (∀ i : Reg, i ≠ 14#5 → T.getReg i = S.getReg i) → R / 2 % 2 = 1 →
      ∃ m S', run m T = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧
        S'.mem = blockCopy N d s (c + R % 4) ∧ CodeAt S' A Code.memcpy ∧
        (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
    intro T hcT hpcT hmT hregT hbit
    have hcb : c + 2 + R % 2 = c + R % 4 := by omega
    refine run_cont (memcpy_blk2 A T (d + BitVec.ofNat 32 c) (s + BitVec.ofNat 32 c) hA hAr hcT hpcT
      (by rw [hregT _ (by decide), h11]) (by rw [hregT _ (by decide), h13]) ?_ ?_ ?_ ?_ ?_) ?_
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · intro S1 ⟨hpc1, h111, h131, hm1, hc1, hreg1⟩
      refine run_cont (memcpy_tail1 A d s N hA hAr n (c + 2) R hd hdn hsn hdisj hR (by omega) S1 hc1
        (Or.inr hpc1) (by rw [h111]; bv_omega) (by rw [h131]; bv_omega)
        (by rw [hreg1 _ (by decide) (by decide) (by decide), hregT _ (by decide), h12])
        (by rw [hm1, hmT, hm, blockCopy_append N d s c 2 (by omega) (by omega) (by omega)])) ?_
      intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
      refine ⟨0, S2, rfl, hpc2, by rw [hm2, hcb], hc2, ?_⟩
      intro i h11 h12 h13 h14
      rw [hreg2 i h11 h12, hreg1 i h14 h11 h13, hregT i h14]
  -- the lower bits only
  have skip : ∀ T : State, CodeAt T A Code.memcpy → T.pc = A + 1976#32 → T.mem = S.mem →
      (∀ i : Reg, i ≠ 14#5 → T.getReg i = S.getReg i) → R / 2 % 2 = 0 →
      ∃ m S', run m T = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧
        S'.mem = blockCopy N d s (c + R % 4) ∧ CodeAt S' A Code.memcpy ∧
        (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
    intro T hcT hpcT hmT hregT hbit
    have hcb : R % 2 = R % 4 := by omega
    refine run_cont (memcpy_tail1 A d s N hA hAr n c R hd hdn hsn hdisj hR (by omega) T hcT
      (Or.inl hpcT) (by rw [hregT _ (by decide), h11]) (by rw [hregT _ (by decide), h13])
      (by rw [hregT _ (by decide), h12]) (by rw [hmT, hm])) ?_
    intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
    refine ⟨0, S2, rfl, hpc2, by rw [hm2, hcb], hc2, ?_⟩
    intro i h11 h12 h13 h14
    rw [hreg2 i h11 h12, hregT i h14]
  by_cases hbit : R / 2 % 2 = 1
  · rw [if_pos hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 492 494
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs)
        (by simp only [jump_mem, next_mem, set_mem]) (fun i hi => by rw [jump_r, next_r, r_set, if_neg hi, getReg_ite_zero])
        hbit
    · rv_code_facts_range hcode Code.memcpy 544 546
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [next_mem, set_mem]) (fun i hi => by rw [next_r, next_r, r_set, if_neg hi, getReg_ite_zero]) hbit
  · have h0 : R / 2 % 2 = 0 := by omega
    rw [if_neg hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 492 494
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact skip _ (codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [next_mem, set_mem]) (fun i hi => by rw [next_r, next_r, r_set, if_neg hi, getReg_ite_zero]) h0
    · rv_code_facts_range hcode Code.memcpy 544 546
      rv_steps 1 with hpc, h12, hand
      rv_branch_taken with hpc
      exact skip _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [jump_mem, next_mem, set_mem]) (fun i hi => by rw [jump_r, next_r, r_set, if_neg hi, getReg_ite_zero]) h0

/-- Decision on bit 2 (`4`) of the remaining count `R` (at `+0x7a8` or `+0x868`), then the 4-byte block if
needed, then the lower bits. -/
theorem memcpy_tail4 (A d s : Word) (N : Word → BitVec 8) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hd4 : d.toNat % 4 = 0) (hs4 : s.toNat % 4 = 0)
    (n c R : Nat) (hd : 4194304 ≤ d.toNat) (hdn : d.toNat + n ≤ 1073741824) (hsn : s.toNat + n ≤ 1073741824)
    (hdisj : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat) (hR : R < 64) (hc4 : c % 4 = 0) (hcn : c + R % 8 ≤ n)
    (S : State) (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 1960#32 ∨ S.pc = A + 2152#32)
    (h11 : S.getReg 11#5 = s + BitVec.ofNat 32 c) (h13 : S.getReg 13#5 = d + BitVec.ofNat 32 c)
    (h12 : S.getReg 12#5 = BitVec.ofNat 32 R) (hm : S.mem = blockCopy N d s c) :
    ∃ m S', run m S = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧ S'.mem = blockCopy N d s (c + R % 8) ∧
      CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
  have hand := and_bit R 2 (by decide)
  simp only [Nat.reducePow] at hand
  -- the 4-byte block (from `+0x870`), then the lower bits
  have blk : ∀ T : State, CodeAt T A Code.memcpy → T.pc = A + 2160#32 → T.mem = S.mem →
      (∀ i : Reg, i ≠ 14#5 → T.getReg i = S.getReg i) → R / 4 % 2 = 1 →
      ∃ m S', run m T = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧
        S'.mem = blockCopy N d s (c + R % 8) ∧ CodeAt S' A Code.memcpy ∧
        (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
    intro T hcT hpcT hmT hregT hbit
    have hcb : c + 4 + R % 4 = c + R % 8 := by omega
    refine run_cont (memcpy_blk4 A T (d + BitVec.ofNat 32 c) (s + BitVec.ofNat 32 c) hA hAr hcT hpcT
      (by rw [hregT _ (by decide), h11]) (by rw [hregT _ (by decide), h13]) ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]; omega
    · intro S1 ⟨hpc1, h111, h131, hm1, hc1, hreg1⟩
      refine run_cont (memcpy_tail2 A d s N hA hAr hd4 hs4 n (c + 4) R hd hdn hsn hdisj hR (by omega) (by omega) S1 hc1
        (Or.inr hpc1) (by rw [h111]; bv_omega) (by rw [h131]; bv_omega)
        (by rw [hreg1 _ (by decide) (by decide) (by decide), hregT _ (by decide), h12])
        (by rw [hm1, hmT, hm, blockCopy_append N d s c 4 (by omega) (by omega) (by omega)])) ?_
      intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
      refine ⟨0, S2, rfl, hpc2, by rw [hm2, hcb], hc2, ?_⟩
      intro i h11 h12 h13 h14
      rw [hreg2 i h11 h12 h13 h14, hreg1 i h14 h11 h13, hregT i h14]
  -- the lower bits only
  have skip : ∀ T : State, CodeAt T A Code.memcpy → T.pc = A + 1968#32 → T.mem = S.mem →
      (∀ i : Reg, i ≠ 14#5 → T.getReg i = S.getReg i) → R / 4 % 2 = 0 →
      ∃ m S', run m T = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧
        S'.mem = blockCopy N d s (c + R % 8) ∧ CodeAt S' A Code.memcpy ∧
        (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
    intro T hcT hpcT hmT hregT hbit
    have hcb : R % 4 = R % 8 := by omega
    refine run_cont (memcpy_tail2 A d s N hA hAr hd4 hs4 n c R hd hdn hsn hdisj hR hc4 (by omega) T hcT
      (Or.inl hpcT) (by rw [hregT _ (by decide), h11]) (by rw [hregT _ (by decide), h13])
      (by rw [hregT _ (by decide), h12]) (by rw [hmT, hm])) ?_
    intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
    refine ⟨0, S2, rfl, hpc2, by rw [hm2, hcb], hc2, ?_⟩
    intro i h11 h12 h13 h14
    rw [hreg2 i h11 h12 h13 h14, hregT i h14]
  by_cases hbit : R / 4 % 2 = 1
  · rw [if_pos hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 490 492
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs)
        (by simp only [jump_mem, next_mem, set_mem]) (fun i hi => by rw [jump_r, next_r, r_set, if_neg hi, getReg_ite_zero])
        hbit
    · rv_code_facts_range hcode Code.memcpy 538 540
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [next_mem, set_mem]) (fun i hi => by rw [next_r, next_r, r_set, if_neg hi, getReg_ite_zero]) hbit
  · have h0 : R / 4 % 2 = 0 := by omega
    rw [if_neg hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 490 492
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact skip _ (codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [next_mem, set_mem]) (fun i hi => by rw [next_r, next_r, r_set, if_neg hi, getReg_ite_zero]) h0
    · rv_code_facts_range hcode Code.memcpy 538 540
      rv_steps 1 with hpc, h12, hand
      rv_branch_taken with hpc
      exact skip _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [jump_mem, next_mem, set_mem]) (fun i hi => by rw [jump_r, next_r, r_set, if_neg hi, getReg_ite_zero]) h0

/-- Decision on bit 3 (`8`) of the remaining count `R` (at `+0x7a0` or `+0x848`), then the 8-byte block if
needed, then the lower bits. -/
theorem memcpy_tail8 (A d s : Word) (N : Word → BitVec 8) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hd4 : d.toNat % 4 = 0) (hs4 : s.toNat % 4 = 0)
    (n c R : Nat) (hd : 4194304 ≤ d.toNat) (hdn : d.toNat + n ≤ 1073741824) (hsn : s.toNat + n ≤ 1073741824)
    (hdisj : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat) (hR : R < 64) (hc4 : c % 4 = 0) (hcn : c + R % 16 ≤ n)
    (S : State) (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 1952#32 ∨ S.pc = A + 2120#32)
    (h11 : S.getReg 11#5 = s + BitVec.ofNat 32 c) (h13 : S.getReg 13#5 = d + BitVec.ofNat 32 c)
    (h12 : S.getReg 12#5 = BitVec.ofNat 32 R) (hm : S.mem = blockCopy N d s c) :
    ∃ m S', run m S = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧ S'.mem = blockCopy N d s (c + R % 16) ∧
      CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
  have hand := and_bit R 3 (by decide)
  simp only [Nat.reducePow] at hand
  -- the 8-byte block (from `+0x850`), then the lower bits
  have blk : ∀ T : State, CodeAt T A Code.memcpy → T.pc = A + 2128#32 → T.mem = S.mem →
      (∀ i : Reg, i ≠ 14#5 → T.getReg i = S.getReg i) → R / 8 % 2 = 1 →
      ∃ m S', run m T = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧
        S'.mem = blockCopy N d s (c + R % 16) ∧ CodeAt S' A Code.memcpy ∧
        (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
    intro T hcT hpcT hmT hregT hbit
    have hcb : c + 8 + R % 8 = c + R % 16 := by omega
    refine run_cont (memcpy_blk8 A T (d + BitVec.ofNat 32 c) (s + BitVec.ofNat 32 c) hA hAr hcT hpcT
      (by rw [hregT _ (by decide), h11]) (by rw [hregT _ (by decide), h13]) ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]; omega
    · intro S1 ⟨hpc1, h111, h131, hm1, hc1, hreg1⟩
      refine run_cont (memcpy_tail4 A d s N hA hAr hd4 hs4 n (c + 8) R hd hdn hsn hdisj hR (by omega) (by omega) S1 hc1
        (Or.inr hpc1) (by rw [h111]; bv_omega) (by rw [h131]; bv_omega)
        (by rw [hreg1 _ (by decide) (by decide) (by decide), hregT _ (by decide), h12])
        (by rw [hm1, hmT, hm, blockCopy_append N d s c 8 (by omega) (by omega) (by omega)])) ?_
      intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
      refine ⟨0, S2, rfl, hpc2, by rw [hm2, hcb], hc2, ?_⟩
      intro i h11 h12 h13 h14
      rw [hreg2 i h11 h12 h13 h14, hreg1 i h14 h11 h13, hregT i h14]
  -- the lower bits only
  have skip : ∀ T : State, CodeAt T A Code.memcpy → T.pc = A + 1960#32 → T.mem = S.mem →
      (∀ i : Reg, i ≠ 14#5 → T.getReg i = S.getReg i) → R / 8 % 2 = 0 →
      ∃ m S', run m T = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧
        S'.mem = blockCopy N d s (c + R % 16) ∧ CodeAt S' A Code.memcpy ∧
        (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
    intro T hcT hpcT hmT hregT hbit
    have hcb : R % 8 = R % 16 := by omega
    refine run_cont (memcpy_tail4 A d s N hA hAr hd4 hs4 n c R hd hdn hsn hdisj hR hc4 (by omega) T hcT
      (Or.inl hpcT) (by rw [hregT _ (by decide), h11]) (by rw [hregT _ (by decide), h13])
      (by rw [hregT _ (by decide), h12]) (by rw [hmT, hm])) ?_
    intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
    refine ⟨0, S2, rfl, hpc2, by rw [hm2, hcb], hc2, ?_⟩
    intro i h11 h12 h13 h14
    rw [hreg2 i h11 h12 h13 h14, hregT i h14]
  by_cases hbit : R / 8 % 2 = 1
  · rw [if_pos hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 488 490
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs)
        (by simp only [jump_mem, next_mem, set_mem]) (fun i hi => by rw [jump_r, next_r, r_set, if_neg hi, getReg_ite_zero])
        hbit
    · rv_code_facts_range hcode Code.memcpy 530 532
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [next_mem, set_mem]) (fun i hi => by rw [next_r, next_r, r_set, if_neg hi, getReg_ite_zero]) hbit
  · have h0 : R / 8 % 2 = 0 := by omega
    rw [if_neg hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 488 490
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact skip _ (codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [next_mem, set_mem]) (fun i hi => by rw [next_r, next_r, r_set, if_neg hi, getReg_ite_zero]) h0
    · rv_code_facts_range hcode Code.memcpy 530 532
      rv_steps 1 with hpc, h12, hand
      rv_branch_taken with hpc
      exact skip _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [jump_mem, next_mem, set_mem]) (fun i hi => by rw [jump_r, next_r, r_set, if_neg hi, getReg_ite_zero]) h0

/-- Decision on bit 4 (`16`) of the remaining count `R` (at `+0x798` or `+0x818`), then the 16-byte block if
needed, then the lower bits. -/
theorem memcpy_tail16 (A d s : Word) (N : Word → BitVec 8) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hd4 : d.toNat % 4 = 0) (hs4 : s.toNat % 4 = 0)
    (n c R : Nat) (hd : 4194304 ≤ d.toNat) (hdn : d.toNat + n ≤ 1073741824) (hsn : s.toNat + n ≤ 1073741824)
    (hdisj : s.toNat + n ≤ d.toNat ∨ d.toNat + n ≤ s.toNat) (hR : R < 64) (hc4 : c % 4 = 0) (hcn : c + R % 32 ≤ n)
    (S : State) (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 1944#32 ∨ S.pc = A + 2072#32)
    (h11 : S.getReg 11#5 = s + BitVec.ofNat 32 c) (h13 : S.getReg 13#5 = d + BitVec.ofNat 32 c)
    (h12 : S.getReg 12#5 = BitVec.ofNat 32 R) (hm : S.mem = blockCopy N d s c) :
    ∃ m S', run m S = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧ S'.mem = blockCopy N d s (c + R % 32) ∧
      CodeAt S' A Code.memcpy ∧
      (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
  have hand := and_bit R 4 (by decide)
  simp only [Nat.reducePow] at hand
  -- the 16-byte block (from `+0x820`), then the lower bits
  have blk : ∀ T : State, CodeAt T A Code.memcpy → T.pc = A + 2080#32 → T.mem = S.mem →
      (∀ i : Reg, i ≠ 14#5 → T.getReg i = S.getReg i) → R / 16 % 2 = 1 →
      ∃ m S', run m T = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧
        S'.mem = blockCopy N d s (c + R % 32) ∧ CodeAt S' A Code.memcpy ∧
        (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
    intro T hcT hpcT hmT hregT hbit
    have hcb : c + 16 + R % 16 = c + R % 32 := by omega
    refine run_cont (memcpy_blk16 A T (d + BitVec.ofNat 32 c) (s + BitVec.ofNat 32 c) hA hAr hcT hpcT
      (by rw [hregT _ (by decide), h11]) (by rw [hregT _ (by decide), h13]) ?_ ?_ ?_ ?_ ?_ ?_) ?_
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega)]; omega
    · rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]; omega
    · intro S1 ⟨hpc1, h111, h131, hm1, hc1, hreg1⟩
      refine run_cont (memcpy_tail8 A d s N hA hAr hd4 hs4 n (c + 16) R hd hdn hsn hdisj hR (by omega) (by omega) S1 hc1
        (Or.inr hpc1) (by rw [h111]; bv_omega) (by rw [h131]; bv_omega)
        (by rw [hreg1 _ (by decide) (by decide) (by decide), hregT _ (by decide), h12])
        (by rw [hm1, hmT, hm, blockCopy_append N d s c 16 (by omega) (by omega) (by omega)])) ?_
      intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
      refine ⟨0, S2, rfl, hpc2, by rw [hm2, hcb], hc2, ?_⟩
      intro i h11 h12 h13 h14
      rw [hreg2 i h11 h12 h13 h14, hreg1 i h14 h11 h13, hregT i h14]
  -- the lower bits only
  have skip : ∀ T : State, CodeAt T A Code.memcpy → T.pc = A + 1952#32 → T.mem = S.mem →
      (∀ i : Reg, i ≠ 14#5 → T.getReg i = S.getReg i) → R / 16 % 2 = 0 →
      ∃ m S', run m T = some S' ∧ (S'.pc = A + 1984#32 ∨ S'.pc = A + 2216#32) ∧
        S'.mem = blockCopy N d s (c + R % 32) ∧ CodeAt S' A Code.memcpy ∧
        (∀ i : Reg, i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → S'.getReg i = S.getReg i) := by
    intro T hcT hpcT hmT hregT hbit
    have hcb : R % 16 = R % 32 := by omega
    refine run_cont (memcpy_tail8 A d s N hA hAr hd4 hs4 n c R hd hdn hsn hdisj hR hc4 (by omega) T hcT
      (Or.inl hpcT) (by rw [hregT _ (by decide), h11]) (by rw [hregT _ (by decide), h13])
      (by rw [hregT _ (by decide), h12]) (by rw [hmT, hm])) ?_
    intro S2 ⟨hpc2, hm2, hc2, hreg2⟩
    refine ⟨0, S2, rfl, hpc2, by rw [hm2, hcb], hc2, ?_⟩
    intro i h11 h12 h13 h14
    rw [hreg2 i h11 h12 h13 h14, hregT i h14]
  by_cases hbit : R / 16 % 2 = 1
  · rw [if_pos hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 486 488
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs)
        (by simp only [jump_mem, next_mem, set_mem]) (fun i hi => by rw [jump_r, next_r, r_set, if_neg hi, getReg_ite_zero])
        hbit
    · rv_code_facts_range hcode Code.memcpy 518 520
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact blk _ (codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [next_mem, set_mem]) (fun i hi => by rw [next_r, next_r, r_set, if_neg hi, getReg_ite_zero]) hbit
  · have h0 : R / 16 % 2 = 0 := by omega
    rw [if_neg hbit] at hand
    rcases hpc with hpc | hpc
    · rv_code_facts_range hcode Code.memcpy 486 488
      rv_steps 1 with hpc, h12, hand
      rv_steps 1 with hpc
      exact skip _ (codeAt_next _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [next_mem, set_mem]) (fun i hi => by rw [next_r, next_r, r_set, if_neg hi, getReg_ite_zero]) h0
    · rv_code_facts_range hcode Code.memcpy 518 520
      rv_steps 1 with hpc, h12, hand
      rv_branch_taken with hpc
      exact skip _ (codeAt_jump _ _ _ _ (codeAt_next _ _ _ (codeAt_set _ _ _ _ _ hcode))) (by rv_regs; rw [hpc]; bv_omega)
        (by simp only [jump_mem, next_mem, set_mem]) (fun i hi => by rw [jump_r, next_r, r_set, if_neg hi, getReg_ite_zero]) h0

end RV
