import Slop.RV.Tactic
import Slop.RV.Code.start

/-! riscv_common's `_start`, `_abs_start`, `_start_rust` (the same bytes in both images): from reset to `main`
(at `0x38`, right after them) with the stack pointer set. -/

namespace RV
set_option maxHeartbeats 400000

/-- From reset (`pc = 0`, any registers): enters `main` with `sp = 0x13ffff0` (two words saved just above it),
`ra` aligned, memory unchanged outside `[0x13ffff8, 0x1400000)`. -/
theorem start_run (S : State) (hpc : S.pc = 0) (hc : CodeAt S 0 Code.start) :
    ∃ m S', run m S = some S' ∧ S'.pc = 0x38#32 ∧ S'.getReg 2#5 = 0x13ffff0#32 ∧ (S'.getReg 1#5).toNat % 4 = 0 ∧
      (∀ a : Word, a.toNat < 0x13ffff8 ∨ 0x1400000 ≤ a.toNat → S'.mem a = S.mem a) := by
  rv_code_facts hc Code.start
  simp only [BitVec.ofNat_eq_ofNat] at *
  rv_steps 14 with hpc
  rv_ret
  refine ⟨by rv_regs <;> (rw [hpc] <;> decide), by rv_regs, by rv_regs <;> decide, ?_⟩
  intro a ha
  simp (disch := rv_disch) only [rv_state, write_outside]

end RV
