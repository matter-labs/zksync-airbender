import Slop.Equiv.Agree
import Slop.Equiv.ExecLoad
import Slop.RV.Input

/-! Our step = an Airbender step for the input read `csrrw rd, 0x7c0, x0` (an Airbender deviation from Sail, which
has no CSR 0x7c0): both sides write the next input word to `rd`. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

variable {s t : RV.State} {σ : SailState} {next : BitVec 32}

theorem exec_input (σ : SailState) (rd : BitVec 5) (hrd : rd ≠ 0) :
    runSail (Airbender.execute next (Airbender.toSail (.inputRead rd))) σ = .ok RETIRE_SUCCESS (xset σ rd next) := by
  simp only [Airbender.toSail, Airbender.execute, regidx_beq_zreg rd hrd]
  simp only [show (regidx.Regidx 0 == zreg) = true from rfl, show ((0x7c0 : BitVec 12) == 0x7c0) = true from rfl,
    Bool.and_true, Bool.true_and]
  simp only [bne, regidx_beq_zreg rd hrd, Bool.not_false, ite_true, Slop.runF_bind, wX_run, Slop.runF_pure]

theorem kind_input (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (rd : BitVec 5)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.inputRead rd)) (hrd : rd ≠ 0) :
    ∃ σ', stepSail next σ = some (σ', true) ∧ Airbender.AgreeSail (s.setReg rd next).nextInstr σ' :=
  step_write h ha h2 _ hdec rd next (exec_input _ rd hrd)

end Slop.Equiv
