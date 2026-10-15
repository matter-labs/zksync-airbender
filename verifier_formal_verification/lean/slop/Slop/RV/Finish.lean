import Slop.RV.Halt
import Slop.RV.CopyRun
import Slop.RV.Code.finish_success
import Slop.RV.Code.finish_success_extended

/-! riscv_common's `zksync_os_finish_success` (the output protocol), at any address. -/

namespace RV
set_option maxHeartbeats 0

/-- riscv_common's `zksync_os_finish_success` (at `A`), called with `a0` pointing to the 8 output words (in RAM, at
or above `sp`): builds the 16-word output array (the 8 words, then 8 zeros) in its frame and jumps to
`zksync_os_finish_success_extended` (linked right after it, at `A + 0x78`) with `a0` pointing to it. -/
theorem finish_success_run (A : Word) (hA : A.toNat % 4 = 0) (hAr : A.toNat + 0x78 ≤ 4194304) (S : State)
    (hc1 : CodeAt S A Code.finish_success)
    (hpc : S.pc = A) (P : Word) (h10 : S.getReg 10#5 = P) (w0 w1 w2 w3 w4 w5 w6 w7 : Word)
    (h0 : read S.mem P 4 = w0) (h1 : read S.mem (P + 4#32) 4 = w1)
    (h2 : read S.mem (P + 8#32) 4 = w2) (h3 : read S.mem (P + 12#32) 4 = w3)
    (h4 : read S.mem (P + 16#32) 4 = w4) (h5 : read S.mem (P + 20#32) 4 = w5)
    (h6 : read S.mem (P + 24#32) 4 = w6) (h7 : read S.mem (P + 28#32) 4 = w7)
    (hsp : (S.getReg 2#5).toNat % 16 = 0) (hsp1 : 4194304 + 128 ≤ (S.getReg 2#5).toNat)
    (hP : (S.getReg 2#5).toNat ≤ P.toNat) (hP4 : P.toNat % 4 = 0) (hP2 : P.toNat + 32 ≤ 1073741824) :
    ∃ m S', run m S = some S' ∧ S'.pc = A + 0x78#32 ∧ S'.getReg 2#5 = S.getReg 2#5 + 4294967216#32 ∧
      S'.getReg 10#5 = S.getReg 2#5 + 4294967224#32 ∧
      read S'.mem (S.getReg 2#5 + 4294967224#32) 4 = w0 ∧ read S'.mem (S.getReg 2#5 + 4294967228#32) 4 = w1 ∧
      read S'.mem (S.getReg 2#5 + 4294967232#32) 4 = w2 ∧ read S'.mem (S.getReg 2#5 + 4294967236#32) 4 = w3 ∧
      read S'.mem (S.getReg 2#5 + 4294967240#32) 4 = w4 ∧ read S'.mem (S.getReg 2#5 + 4294967244#32) 4 = w5 ∧
      read S'.mem (S.getReg 2#5 + 4294967248#32) 4 = w6 ∧ read S'.mem (S.getReg 2#5 + 4294967252#32) 4 = w7 ∧
      read S'.mem (S.getReg 2#5 + 4294967256#32) 4 = 0 ∧ read S'.mem (S.getReg 2#5 + 4294967260#32) 4 = 0 ∧
      read S'.mem (S.getReg 2#5 + 4294967264#32) 4 = 0 ∧ read S'.mem (S.getReg 2#5 + 4294967268#32) 4 = 0 ∧
      read S'.mem (S.getReg 2#5 + 4294967272#32) 4 = 0 ∧ read S'.mem (S.getReg 2#5 + 4294967276#32) 4 = 0 ∧
      read S'.mem (S.getReg 2#5 + 4294967280#32) 4 = 0 ∧ read S'.mem (S.getReg 2#5 + 4294967284#32) 4 = 0 ∧
      (∀ b : Word, b.toNat < ROM_END → S'.mem b = S.mem b) := by
  rv_code_facts hc1 Code.finish_success
  rv_steps 30 with hpc, h10, h0, h1, h2, h3, h4, h5, h6, h7
  rv_ret
  refine ⟨by rv_regs <;> (rw [hpc] <;> bv_omega), by rv_regs, by rv_regs, ?_⟩
  simp (disch := first | decide | rv_disch) only [rv_state, read_write_off, read_write_off0l, read_write_off0r,
    read_write_same4, true_and]
  intro b hb
  simp (disch := first | assumption | (simp only [writable, ROM_END, RAM_END]; bv_omega)) only [rv_state, write_rom]
end RV
