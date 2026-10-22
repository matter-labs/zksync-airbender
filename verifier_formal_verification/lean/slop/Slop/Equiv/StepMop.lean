import Slop.Equiv.Agree
import Slop.Equiv.ExecLoad

/-! Our step = an Airbender step for the field operations `mop.rr.N` and `mop.r.N` (Airbender deviations from
Sail, where Zimop writes 0: both sides compute `RV.mopVal`, or `(rd ^^^ rs1)` rotated right), and for `rev8`. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

variable {s t : RV.State} {σ : SailState} {next : BitVec 32}

theorem mopOfIndex_mopIndex (op : RV.FieldOp) : Airbender.mopOfIndex (Airbender.mopIndex op) = some op := by
  cases op <;> rfl

theorem exec_mop (σ : SailState) (op : RV.FieldOp) (rd rs1 rs2 : BitVec 5) :
    runSail (Airbender.execute next (Airbender.toSail (.mop op rd rs1 rs2))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (RV.mopVal op (xget σ rs1) (xget σ rs2) (xget σ rd))) := by
  simp only [Airbender.toSail, Airbender.execute, mopOfIndex_mopIndex, Slop.runF_bind, rX_run, wX_run, Slop.runF_pure]

theorem kind_mop (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (op : RV.FieldOp) (rd rs1 rs2 : BitVec 5)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.mop op rd rs1 rs2))
    (ht : RV.exec s (.mop op rd rs1 rs2) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec, Option.some.injEq] at ht; subst ht
  have e := exec_mop (next := next) (σ.set .nextPC (σ.regs .PC + 4)) op rd rs1 rs2
  rw [xget_set_nextPC, xget_set_nextPC, xget_set_nextPC, agree_xget h, agree_xget h, agree_xget h] at e
  exact step_write h ha h2 _ hdec rd _ e

theorem exec_xorrot (σ : SailState) (n : BitVec 5) (rd rs1 : BitVec 5) :
    runSail (Airbender.execute next (Airbender.toSail (.xorRot n rd rs1))) σ =
      .ok RETIRE_SUCCESS (xset σ rd ((xget σ rd ^^^ xget σ rs1).rotateRight n.toNat)) := by
  simp only [Airbender.toSail, Airbender.execute, Slop.runF_bind, rX_run, wX_run, Slop.runF_pure]

theorem kind_xorrot (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (n : BitVec 5) (rd rs1 : BitVec 5)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.xorRot n rd rs1))
    (ht : RV.exec s (.xorRot n rd rs1) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec, Option.some.injEq] at ht; subst ht
  have e := exec_xorrot (next := next) (σ.set .nextPC (σ.regs .PC + 4)) n rd rs1
  rw [xget_set_nextPC, xget_set_nextPC, agree_xget h, agree_xget h] at e
  exact step_write h ha h2 _ hdec rd _ e

/-- Sail's `rev8` (a loop over the bytes) is ours. -/
theorem rev8_eq (x : BitVec 32) : SailRV32.Functions.rev8 x = RV.rev8 x := by
  simp only [SailRV32.Functions.rev8, Id.run, Sail.BitVec.length]
  rw [forIn_eq_forIn']
  simp only [ForIn'.forIn', IntRange.forIn']
  repeat (rw [IntRange.forIn'.loop]; simp [Membership.mem])
  dsimp only [pure]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [RV.rev8, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  interval_cases j <;> simp [Sail.BitVec.extractLsb]

theorem exec_rev8 (σ : SailState) (rd rs1 : BitVec 5) :
    runSail (Airbender.execute next (Airbender.toSail (.rev8 rd rs1))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (RV.rev8 (xget σ rs1))) := by
  simp only [Airbender.toSail, Airbender.execute, execute, execute_REV8, Slop.runF_bind, rX_run, wX_run,
    Slop.runF_pure, rev8_eq]

theorem kind_rev8 (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (rd rs1 : BitVec 5)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.rev8 rd rs1))
    (ht : RV.exec s (.rev8 rd rs1) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec, Option.some.injEq] at ht; subst ht
  have e := exec_rev8 (next := next) (σ.set .nextPC (σ.regs .PC + 4)) rd rs1
  rw [xget_set_nextPC, agree_xget h] at e
  exact step_write h ha h2 _ hdec rd _ e

end Slop.Equiv
