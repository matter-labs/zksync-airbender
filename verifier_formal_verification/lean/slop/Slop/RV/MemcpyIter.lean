import Slop.RV.CopyRun
import Slop.RV.Code.memcpy

/-! `memcpy` (riscv_common's, as linked by the real Airbender guests), aligned path: one iteration of its unrolled
64-byte loop. General in the code's address, the pointers and the memory. -/

namespace RV
set_option maxHeartbeats 400000

set_option maxRecDepth 100000 in
theorem memcpy_length : Code.memcpy.length = 1676 := rfl

/-- One iteration of `memcpy`'s 64-byte loop (`memcpy + 0x58` up to its back-branch at `+0xe4`): 64 bytes from
`q` (`a1`) to `p` (`a3`); `a1`, `a3` advance by 64, `a2` decreases by 64; registers other than `a1`, `a2`, `a3`, `a5`
unchanged. -/
theorem memcpy_iter (A : Word) (S : State) (p q r : Word)
    (hA : A.toNat % 4 = 0) (hAr : A.toNat + 4 * 1676 ≤ 4194304)
    (hcode : CodeAt S A Code.memcpy) (hpc : S.pc = A + 88#32) (h11 : S.getReg 11#5 = q) (h13 : S.getReg 13#5 = p)
    (h12 : S.getReg 12#5 = r)
    (hp : 4194304 ≤ p.toNat) (hp2 : p.toNat + 64 ≤ 1073741824) (hp4 : p.toNat % 4 = 0) (hq4 : q.toNat % 4 = 0)
    (hq : q.toNat + 64 ≤ 1073741824) (hdisj : q.toNat + 64 ≤ p.toNat ∨ p.toNat + 64 ≤ q.toNat) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 228#32 ∧ S'.getReg 11#5 = q + 64#32 ∧ S'.getReg 13#5 = p + 64#32 ∧
      S'.getReg 12#5 = r + 4294967232#32 ∧ S'.mem = blockCopy S.mem p q 64 ∧
      (∀ i : Reg, i ≠ 15#5 → i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → S'.getReg i = S.getReg i) := by
  rv_code_facts_range hcode Code.memcpy 22 52
  obtain ⟨S1, hrun1, hpc1, hm1, hreg1⟩ := run_copy_pairs 15#5 11#5 13#5 (by decide) (by decide) (by decide) (by decide)
    (by decide) S.mem p q 15 S (A + 88#32) 0 hpc (by bv_omega) (by simp only [ROM_END]; bv_omega)
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
  have h12' : S1.getReg 12#5 = r := by rw [hreg1 _ (by decide), h12]
  simp only [Nat.reduceMul, Nat.zero_add] at hpc1 hm1
  rv_code_facts_range hc1 Code.memcpy 52 57
  rv_steps 5 with hpc1, h11', h13', h12'
  rv_ret
  refine ⟨by rv_regs; rw [hpc1]; bv_omega, by rv_regs, by rv_regs, by rv_regs, ?_, ?_⟩
  · simp only [rv_state, h11', h13', hm1]
    rw [read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)]
    exact copy_step _ p q 60 4 (by omega) (by omega)
  · intro i h15 h11 h12 h13
    by_cases h0 : i = 0
    · subst h0; rfl
    · simp only [next_r, store_r, r_set, h0, h15, h11, h12, h13, ite_false, hreg1 i h15]
end RV
