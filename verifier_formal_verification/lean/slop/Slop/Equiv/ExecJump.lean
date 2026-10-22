import Slop.Equiv.Jump

/-! Sail's `execute` on our control-flow instructions (branches, JAL, JALR): same target, same link value. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
variable {next : BitVec 32}

theorem sext_n {n : Nat} (x : BitVec n) (hn : 0 < n) (h32 : n ≤ 32) :
    sign_extend (m := 32) ((x.signExtend 32).extractLsb' 0 n) = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb']
  by_cases h : j < n <;> simp [h, hj, BitVec.msb_eq_getLsbD_last, BitVec.getMsbD_eq_getLsbD, BitVec.getElem_signExtend]
  rw [show 31 - (32 - n) = n - 1 by omega]
  simp [BitVec.getLsbD_signExtend, hn, h32, show n - 1 < n by omega, show n - 1 < 32 by omega, BitVec.getElem_signExtend]

theorem blt_eq (a b : BitVec 32) : zopz0zI_s a b = a.slt b := by simp [zopz0zI_s, BitVec.slt]
theorem bge_eq (a b : BitVec 32) : zopz0zKzJ_s a b = !a.slt b := by
  by_cases h : a.toInt < b.toInt <;> simp [zopz0zKzJ_s, BitVec.slt, h] <;> omega
theorem bltu_eq (a b : BitVec 32) : zopz0zI_u a b = a.ult b := by simp [zopz0zI_u, BitVec.toNatInt, BitVec.ult]
theorem bgeu_eq (a b : BitVec 32) : zopz0zKzJ_u a b = !a.ult b := by
  by_cases h : a.toNat < b.toNat <;> simp [zopz0zKzJ_u, BitVec.toNatInt, BitVec.ult, h] <;> omega

theorem exec_branch (σ : SailState) (hs : Airbender.Configured σ) (c : RV.Cond) (rs1 rs2 : BitVec 5) (x : BitVec 13)
    (hal : c.holds (xget σ rs1) (xget σ rs2) = true → (σ.regs .PC + x.signExtend 32).toNat % 4 = 0) :
    runSail (Airbender.execute next (Airbender.toSail (.branch c rs1 rs2 (x.signExtend 32)))) σ =
      if c.holds (xget σ rs1) (xget σ rs2) then .ok RETIRE_SUCCESS (σ.set .nextPC (σ.regs .PC + x.signExtend 32))
      else .ok RETIRE_SUCCESS σ := by
  have hx := sext_n x (by decide) (by decide)
  cases c
  all_goals simp only [Airbender.toSail, Airbender.sailBranchOp, Airbender.execute, execute, execute_BTYPE, Slop.runF_bind, rX_run,
    Slop.runF_pure, blt_eq, bge_eq, bltu_eq, bgeu_eq, RV.Cond.holds] at hal ⊢
  all_goals (split <;> rename_i hc <;> simp only [hc, ↓reduceIte])
  all_goals first
    | (rw [Slop.runF_bind, Slop.runF_readReg]; simp only [hx]; exact jump_to_run σ hs _ (hal hc))
    | (rw [Slop.runF_pure]; simp)

theorem exec_jal (σ : SailState) (hs : Airbender.Configured σ) (rd : BitVec 5) (x : BitVec 21)
    (hal : (σ.regs .PC + x.signExtend 32).toNat % 4 = 0) :
    runSail (Airbender.execute next (Airbender.toSail (.jal rd (x.signExtend 32)))) σ =
      .ok RETIRE_SUCCESS (xset (σ.set .nextPC (σ.regs .PC + x.signExtend 32)) rd (σ.regs .nextPC)) := by
  have hx := sext_n x (by decide) (by decide)
  simp only [Airbender.toSail, Airbender.execute, execute, execute_JAL, Slop.runF_bind, get_next_pc, hx]
  rw [Slop.runF_readReg]; dsimp only
  rw [Slop.runF_readReg]; dsimp only
  rw [jump_to_run σ hs _ hal]; dsimp only
  simp only [RETIRE_SUCCESS, Slop.runF_bind, wX_run, Slop.runF_pure]

theorem clear_bit0 (t : BitVec 32) : BitVec.update t 0 0#1 = t &&& ~~~1 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.update, Sail.BitVec.updateSubrange']
  interval_cases j <;> simp

theorem exec_jalr (σ : SailState) (hs : Airbender.Configured σ) (rd rs1 : BitVec 5) (x : BitVec 12)
    (hal : ((xget σ rs1 + x.signExtend 32) &&& ~~~1).toNat % 4 = 0) :
    runSail (Airbender.execute next (Airbender.toSail (.jalr rd rs1 (x.signExtend 32)))) σ =
      .ok RETIRE_SUCCESS (xset (σ.set .nextPC ((xget σ rs1 + x.signExtend 32) &&& ~~~1)) rd (σ.regs .nextPC)) := by
  have hx := sext_n x (by decide) (by decide)
  have hz : runSail (currentlyEnabled .Ext_Zicfilp) σ = .ok false σ := oracle_run hs _ _ (by decide +kernel)
  simp only [Airbender.toSail, Airbender.execute, execute, execute_JALR, Slop.runF_bind, update_elp_state, hz,
    get_next_pc, rX_run, hx, clear_bit0, Bool.false_eq_true, ↓reduceIte, Slop.runF_pure]
  rw [Slop.runF_readReg]; dsimp only
  rw [jump_to_run σ hs _ hal]; dsimp only
  simp only [RETIRE_SUCCESS, Slop.runF_bind, wX_run, Slop.runF_pure]

end Slop.Equiv
