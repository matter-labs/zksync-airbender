import Slop.RV.Tactic
import Slop.RV.Code.inc

namespace RV

theorem inc_impl : Implements Code.inc 16 (mapsA0 (· + 1)) := by
  intro s hcall
  rv_start Code.inc hcall
  rv_steps 9
  rv_ret
  exact ⟨by rv_regs, by rv_regs, by rv_callee, by rv_frame⟩

end RV
