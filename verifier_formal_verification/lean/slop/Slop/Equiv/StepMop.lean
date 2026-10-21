import Slop.Equiv.Agree
import Slop.Equiv.ExecLoad

/-! Our step = an Airbender step for the field operations `mop.rr.N` (an Airbender deviation from Sail, where
Zimop writes 0: both sides compute `RV.mopVal`). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

variable {s t : RV.State} {σ : SailState} {next : BitVec 32}

theorem mopOfIndex_mopIndex (op : RV.FieldOp) : Airbender.mopOfIndex (Airbender.mopIndex op) = some op := by
  cases op <;> rfl

theorem exec_mop (σ : SailState) (op : RV.FieldOp) (rd rs1 rs2 : BitVec 5) (hrd : rd ≠ 0) :
    runSail (Airbender.execute next (Airbender.toSail (.mop op rd rs1 rs2))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (RV.mopVal op (xget σ rs1) (xget σ rs2) (xget σ rd))) := by
  simp only [Airbender.toSail, Airbender.execute, mopOfIndex_mopIndex, regidx_beq_zreg rd hrd, Bool.false_eq_true,
    ite_false, Slop.runF_bind, rX_run, wX_run, Slop.runF_pure]

theorem kind_mop (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (op : RV.FieldOp) (rd rs1 rs2 : BitVec 5)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.mop op rd rs1 rs2))
    (ht : RV.exec s (.mop op rd rs1 rs2) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec] at ht
  by_cases hrd : rd = 0
  · rw [if_pos hrd] at ht; cases ht
  rw [if_neg hrd, Option.some.injEq] at ht; subst ht
  have e := exec_mop (next := next) (σ.set .nextPC (σ.regs .PC + 4)) op rd rs1 rs2 hrd
  rw [xget_set_nextPC, xget_set_nextPC, xget_set_nextPC, agree_xget h, agree_xget h, agree_xget h] at e
  exact step_write h ha h2 _ hdec rd _ e

end Slop.Equiv
