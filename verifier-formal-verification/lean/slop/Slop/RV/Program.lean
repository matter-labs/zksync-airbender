import Slop.RV.Combine
import Slop.RV.Poly
import Slop.RV.Code.boot
import Slop.RV.Coeffs

set_option maxHeartbeats 0

namespace RV

/-- From reset (pc = 0, any registers) with the code in memory and a field element `x` at `INPUT`, the program
reaches `_halt` with `a0 = 3x + 1` and `a1 ≡ polyW COEFFS x (mod P)`, `a1 ≤ P`, with the boot code (which holds
the `_halt` loop) still in memory. -/
theorem program_run (s : State) (x : Word) (hpc : s.pc = 0)
    (hboot : CodeAt s 0 Code.boot) (hcomb : CodeAt s 0xbc Code.combine)
    (hinc : CodeAt s 0x128 Code.inc) (hdbl : CodeAt s 0x104 Code.double)
    (hpoly : CodeAt s 0x188 Code.poly_eval) (hmul : CodeAt s 0x14c Code.mul_mod)
    (hadd : CodeAt s 0x88 Code.add_mod) (hcoef : CodeAt s 0x204 Code.COEFFS)
    (hin : read s.mem 0x4400000 4 = x) (hx : x.toNat ≤ P) :
    ∃ n s', run n s = some s' ∧ s'.pc = 0x38 ∧ s'.r 10 = 3 * x + 1 ∧
      (s'.r 11).toNat ≤ P ∧ (s'.r 11).toNat % P = polyW Code.COEFFS x.toNat % P ∧
      CodeAt s' 0 Code.boot := by
  simp only [BitVec.ofNat_eq_ofNat] at hpc hboot hcomb hinc hdbl hpoly hmul hadd hcoef hin ⊢
  rv_code_facts hboot Code.boot
  rv_steps 24 with hpc, hin
  apply run_callAt (combine_impl 0xbc#32 (by decide))
  · rv_regs
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h <;> subst h
    · rv_codeAt hinc Code.inc
    · rv_codeAt hdbl Code.double
  · rv_call_ok hcomb Code.combine
  rv_returned S1 hpc1 hpost1 hcs1 hmem1
  rv_steps 5 with hpc1, hcs1, read_of_frame hmem1
  apply run_callAtPre (poly_eval_impl 0x188#32 (by decide) Code.COEFFS coeffs_le)
  · rv_regs
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h <;> subst h
    · rv_codeAt hmul Code.mul_mod with hcs1
    · rv_codeAt hadd Code.add_mod with hcs1
  · rv_call_ok hpoly Code.poly_eval with hcs1
  · simp only [polyPre]
    rv_regs
    refine ⟨(by rv_codeAt hcoef Code.COEFFS with hcs1), (by rw [coeffs_length]), (by rw [coeffs_length]; decide),
      (by decide), hx⟩
  rv_returned S2 hpc2 hpost2 hcs2 hmem2 with hcs1
  rv_steps 3 with hpc2, hcs2, hcs1, read_of_frame hmem2, read_of_frame hmem1
  rv_ret
  refine ⟨by rv_regs, by rv_regs; exact hpost1, ?_, ?_, ?_⟩
  · rv_regs; exact hpost2.1
  · rv_regs; exact hpost2.2
  · rv_codeAt hboot Code.boot with hcs2, hcs1

end RV
