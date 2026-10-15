import Slop.RV.Halt
import Slop.RV.CopyRun
import Slop.RV.Code.finish_success_extended

/-! riscv_common's `zksync_os_finish_success_extended`, at any address: the outputs land in `x10 … x25`. -/

namespace RV
set_option maxHeartbeats 0

/-- riscv_common's `zksync_os_finish_success_extended` (at `A`), with `a0` pointing to the 16-word output array
(at `sp + 8`, as `zksync_os_finish_success` calls it): loads the words into `x10 … x25` and reaches its final
self-jump (`A + 0x80`). -/
theorem finish_extended_run (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 0x84 ≤ 4194304) (S : State)
    (hc : CodeAt S A Code.finish_success_extended)
    (hpc : S.pc = A) (h10 : S.getReg 10#5 = S.getReg 2#5 + 8#32)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : Word)
    (hm0 : read S.mem (S.getReg 2#5 + 8#32) 4 = r0) (hm1 : read S.mem (S.getReg 2#5 + 12#32) 4 = r1) (hm2 : read S.mem (S.getReg 2#5 + 16#32) 4 = r2) (hm3 : read S.mem (S.getReg 2#5 + 20#32) 4 = r3) (hm4 : read S.mem (S.getReg 2#5 + 24#32) 4 = r4) (hm5 : read S.mem (S.getReg 2#5 + 28#32) 4 = r5) (hm6 : read S.mem (S.getReg 2#5 + 32#32) 4 = r6) (hm7 : read S.mem (S.getReg 2#5 + 36#32) 4 = r7) (hm8 : read S.mem (S.getReg 2#5 + 40#32) 4 = r8) (hm9 : read S.mem (S.getReg 2#5 + 44#32) 4 = r9) (hm10 : read S.mem (S.getReg 2#5 + 48#32) 4 = r10) (hm11 : read S.mem (S.getReg 2#5 + 52#32) 4 = r11) (hm12 : read S.mem (S.getReg 2#5 + 56#32) 4 = r12) (hm13 : read S.mem (S.getReg 2#5 + 60#32) 4 = r13) (hm14 : read S.mem (S.getReg 2#5 + 64#32) 4 = r14) (hm15 : read S.mem (S.getReg 2#5 + 68#32) 4 = r15)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 64 ≤ (S.getReg 2#5).toNat)
    (hsp2 : (S.getReg 2#5).toNat + 128 ≤ 1073741824) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 0x80#32 ∧ S'.getReg 10#5 = r0 ∧ S'.getReg 11#5 = r1 ∧ S'.getReg 12#5 = r2 ∧ S'.getReg 13#5 = r3 ∧ S'.getReg 14#5 = r4 ∧ S'.getReg 15#5 = r5 ∧ S'.getReg 16#5 = r6 ∧ S'.getReg 17#5 = r7 ∧ S'.getReg 18#5 = r8 ∧ S'.getReg 19#5 = r9 ∧ S'.getReg 20#5 = r10 ∧ S'.getReg 21#5 = r11 ∧ S'.getReg 22#5 = r12 ∧ S'.getReg 23#5 = r13 ∧ S'.getReg 24#5 = r14 ∧ S'.getReg 25#5 = r15 ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) := by
  rv_code_facts hc Code.finish_success_extended
  rv_steps 32 with hpc, h10, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15
  rv_ret
  refine ⟨by rv_regs <;> (rw [hpc] <;> bv_omega), by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, by rv_regs, ?_⟩
  intro b hb
  simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END]; bv_omega)) only [rv_state, write_rom]
end RV
