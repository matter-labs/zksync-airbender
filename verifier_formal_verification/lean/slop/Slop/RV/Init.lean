import Slop.RV.Memcpy
import Slop.RV.Code.init

/-! riscv_common's `boot_sequence::init` (as linked by the real Airbender guests): copies `.rodata` and `.data`
from ROM to RAM with `memcpy`. -/

namespace RV
set_option maxHeartbeats 0

set_option hygiene false in
/-- The proof of `init_run` for an image's `init` code `code`, whose `.rodata` (912 bytes) is at ROM `src`. -/
macro "init_run_proof" code:ident src:term : tactic => `(tactic| (
    rv_code_facts hcode $code
    rv_steps 20 with hpc
    rv_name T hT
    have hTrom : ∀ b : Word, b.toNat < ROM_END → T.mem b = S.mem b := by
      intro b hb; rw [← hT]; simp only [rv_state]
      rw [write_rom _ _ _ _ (by simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb,
        write_rom _ _ _ _ (by simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb]
    refine run_cont (memcpy_aligned (A + 136#32) (by bv_omega) (by bv_omega) T 20971520#32 $src 912
      (codeAt_of_rom hmc (by rw [memcpy_length]; simp only [ROM_END]; bv_omega) hTrom)
      (by rw [← hT]; rv_regs) (by rw [← hT]; rv_regs) (by rw [← hT]; rv_regs)
      (by rw [← hT]; rv_regs; decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [← hT]; rv_regs; bv_omega) (by rw [← hT]; rv_regs; bv_omega) (by rw [← hT]; rv_regs; bv_omega)
      (by rw [← hT]; rv_regs; bv_omega) (by rw [← hT]; rv_regs; bv_omega) (by rw [← hT]; rv_regs; bv_omega)) ?_
    intro S1 ⟨hpc1, hm1, h21, hc1, hreg1⟩
    have hTm : T.mem = write (write S.mem (S.getReg 2#5 + 4294967292#32) (S.getReg 1#5) 4)
        (S.getReg 2#5 + 4294967288#32) (S.getReg 8#5) 4 := by rw [← hT]; simp only [rv_state]
    have hT2 : T.getReg 2#5 = S.getReg 2#5 + 4294967280#32 := by rw [← hT]; rv_regs
    have hS1rom : ∀ b : Word, b.toNat < ROM_END → S1.mem b = S.mem b := by
      intro b hb
      rw [hm1, blockCopy_rom _ _ _ _ (by decide) (by decide) _ hb,
        write_rom _ _ _ _ (by rw [hT2]; simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb,
        write_rom _ _ _ _ (by rw [hT2]; simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb, hTrom b hb]
    have hc1' : CodeAt S1 A $code :=
      codeAt_of_rom hcode (by rw [show ($code).length = 34 from rfl]; simp only [ROM_END]; bv_omega) hS1rom
    have hra1 : read S1.mem (S.getReg 2#5 + 4294967292#32) 4 = S.getReg 1#5 := by
      rw [hm1, read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), hT2,
        read_write_disjoint _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
        read_write_disjoint _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), hTm,
        read_write_disjoint _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), read_write_same4]
    have hs01 : read S1.mem (S.getReg 2#5 + 4294967288#32) 4 = S.getReg 8#5 := by
      rw [hm1, read_blockCopy_outside _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), hT2,
        read_write_disjoint _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega),
        read_write_disjoint _ _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega), hTm, read_write_same4]
    have h21' : S1.getReg 2#5 = S.getReg 2#5 + 4294967280#32 := by rw [h21, hT2]
    rv_clear_facts
    rv_code_facts hc1' $code
    have hpc1' : S1.pc = A + 80#32 := by rw [hpc1, ← hT]; rv_regs
    rv_steps 11 with hpc1', h21', hra1, hs01
    rv_name T2 hT2'
    have hT2m : T2.mem = S1.mem := by rw [← hT2']; simp only [rv_state]
    have hT2sp : T2.getReg 2#5 = S.getReg 2#5 := by rw [← hT2']; rv_regs
    refine run_cont (memcpy_aligned (A + 136#32) (by bv_omega) (by bv_omega) T2 20975616#32 16384#32 0
      (codeAt_of_rom hc1 (by rw [memcpy_length]; simp only [ROM_END]; bv_omega) (fun b _ => by rw [hT2m]))
      (by rw [← hT2']; rv_regs) (by rw [← hT2']; rv_regs) (by rw [← hT2']; rv_regs) (by rw [← hT2']; rv_regs; decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hT2sp]; exact hsp) (by rw [hT2sp]; omega) (by rw [hT2sp]; omega)
      (by rw [← hT2']; rv_regs; exact hra) (by rw [hT2sp]; right; simp; omega) (by rw [hT2sp]; left; simp; omega)) ?_
    intro S2 ⟨hpc2, hm2, h22, hc2, hreg2⟩
    refine ⟨0, S2, rfl, by rw [hpc2, ← hT2']; rv_regs, ?_, ?_, ?_⟩
    · intro a ha
      have hT2r1 : T2.getReg 1#5 = S.getReg 1#5 := by rw [← hT2']; rv_regs
      have hT2r8 : T2.getReg 8#5 = S.getReg 8#5 := by rw [← hT2']; rv_regs
      rw [hm2, blockCopy_zero, hT2sp, write_outside _ _ _ _ _ (by bv_omega) (by bv_omega),
        write_outside _ _ _ _ _ (by bv_omega) (by bv_omega), hT2m, hm1, hT2]
      simp only [blockCopy]
      split
      · rw [write_rom _ _ _ _ (by simp only [writable, ROM_END, RAM_END]; bv_omega) _ (by simp only [ROM_END]; bv_omega),
          write_rom _ _ _ _ (by simp only [writable, ROM_END, RAM_END]; bv_omega) _ (by simp only [ROM_END]; bv_omega),
          hTrom _ (by simp only [ROM_END]; bv_omega)]
      · rw [write_outside _ _ _ _ _ (by bv_omega) (by bv_omega), write_outside _ _ _ _ _ (by bv_omega) (by bv_omega), hTm,
          write_outside _ _ _ _ _ (by bv_omega) (by bv_omega), write_outside _ _ _ _ _ (by bv_omega) (by bv_omega)]
    · intro b hb
      rw [hm2, blockCopy_rom _ _ _ _ (by decide) (by decide) _ hb,
        write_rom _ _ _ _ (by rw [hT2sp]; simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb,
        write_rom _ _ _ _ (by rw [hT2sp]; simp only [writable, ROM_END, RAM_END]; bv_omega) _ hb, hT2m, hS1rom b hb]
    · intro i h10 h11 h12 h13 h14 h15
      rw [hreg2 i h11 h12 h13 h14 h15, ← hT2']
      by_cases h1 : i = 1#5
      · subst h1; rv_regs
      by_cases h2 : i = 2#5
      · subst h2; rv_regs
      by_cases h8 : i = 8#5
      · subst h8; rv_regs
      by_cases h0 : i = 0#5
      · subst h0; rw [r_zero5, r_zero5]
      simp only [rv_state, r_set, jump_r, next_r, h0, h1, h2, h8, h10, h11, h12, ite_false, show ¬ (i = 0) from h0]
      rw [hreg1 i h11 h12 h13 h14 h15, ← hT]
      simp only [rv_state, r_set, jump_r, next_r, h0, h1, h2, h8, h10, h11, h12, h13, ite_false, show ¬ (i = 0) from h0]
))

/-- `init` at `A` (with `memcpy` right after it, at `A + 136`): copies `.rodata` (912 bytes, from ROM `0x24b0`
to RAM `0x1400000`) and its empty `.data`; returns to `ra` with the memory outside its frames a block copy,
ROM unchanged, and every register outside `a0 … a5` restored or untouched. -/
theorem init_run (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 136 + 4 * 1676 ≤ 4194304) (S : State)
    (hcode : CodeAt S A Code.init) (hmc : CodeAt S (A + 136#32) Code.memcpy) (hpc : S.pc = A)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 32 ≤ (S.getReg 2#5).toNat)
    (hsp2 : (S.getReg 2#5).toNat ≤ 20971520) (hra : (S.getReg 1#5).toNat % 4 = 0) :
    ∃ m S', run m S = some S' ∧ S'.pc = S.getReg 1#5 ∧
      (∀ a : Word, a.toNat + 32 < (S.getReg 2#5).toNat ∨ (S.getReg 2#5).toNat ≤ a.toNat →
        S'.mem a = blockCopy S.mem 20971520#32 9392#32 912 a) ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) ∧
      (∀ i : Reg, i ≠ 10#5 → i ≠ 11#5 → i ≠ 12#5 → i ≠ 13#5 → i ≠ 14#5 → i ≠ 15#5 → S'.getReg i = S.getReg i) := by
  init_run_proof Code.init 9392#32

end RV
