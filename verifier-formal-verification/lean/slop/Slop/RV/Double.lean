import Slop.RV.Tactic
import Slop.RV.Code.double

namespace RV

theorem double_impl : Implements Code.double 16 (fn₁ (2 * ·)) := by
  intro s hcall
  rv_start Code.double hcall
  rv_steps 9
  rv_ret
  refine ⟨by rv_regs, ?_, by rv_callee, by rv_frame⟩
  rv_regs
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_mul]
  omega

end RV
