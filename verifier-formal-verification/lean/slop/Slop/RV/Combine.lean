import Slop.RV.Inc
import Slop.RV.Double
import Slop.RV.Code.combine

set_option maxHeartbeats 1000000

namespace RV

/-- `combine` at any address `A`, calling `inc` and `double` at their relative offsets (`A + 0x6c`, `A + 0x48`). -/
theorem combine_impl (A : Word) (hA : A.toNat + 0x6c + 36 ≤ 4194304) :
    ImplementsAt A Code.combine [(A + 0x6c#32, Code.inc), (A + 0x48#32, Code.double)] 32 (fn₁ (3 * · + 1)) := by
  intro s hentry hcallees hcall
  have hinc : CodeAt s (A + 0x6c#32) Code.inc := hcallees (A + 0x6c#32, Code.inc) (by simp)
  have hdbl : CodeAt s (A + 0x48#32) Code.double := hcallees (A + 0x48#32, Code.double) (by simp)
  clear hcallees
  rw [Call, hentry] at hcall
  rv_start Code.combine hcall
  rv_steps 8 with hentry
  apply run_call inc_impl
  · rv_call_ok hinc Code.inc
  rv_returned S1 hpc1 hpost1 hcs1 hmem1
  rv_steps 3 with hpc1, hpost1, hcs1, read_of_frame hmem1
  apply run_call double_impl
  · rv_call_ok hdbl Code.double with hcs1
  rv_returned S2 hpc2 hpost2 hcs2 hmem2
  rv_steps 7 with hpc2, hpost2, hcs2, read_of_frame hmem2, hcs1, read_of_frame hmem1
  rv_ret
  exact ⟨by rv_regs, by rv_regs; bv_omega, (by rv_callee with hcs2, hcs1), (by rv_frame with hmem2, hmem1, hcs1)⟩

end RV
