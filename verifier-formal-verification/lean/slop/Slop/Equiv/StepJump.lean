import Slop.Equiv.StepAlu
import Slop.Equiv.ExecJump

/-! Our step = an Airbender step, for JAL, JALR and branches. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

variable {s t : RV.State} {σ : FState}

theorem set1_PC (σ : FState) (v : BitVec 32) (h : σ.regs .PC = s.pc) : (σ.set .nextPC v).regs .PC = s.pc := by
  rw [set_regs_ne _ _ _ _ (by decide)]; exact h

theorem kind_jal (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (rd : BitVec 5) (x : BitVec 21)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.jal rd (x.signExtend 32)))
    (ht : RV.exec s (.jal rd (x.signExtend 32)) = some t) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree t σ' := by
  simp only [RV.exec, RV.State.goto] at ht
  split_ifs at ht with hT
  case neg => simp at ht
  simp only [Option.map_some, Option.some.injEq] at ht; subst ht
  have hp := set1_PC σ (σ.regs .PC + 4) h.2.1
  have hn : (σ.set .nextPC (σ.regs .PC + 4)).regs .nextPC = s.pc + 4 := by rw [set_regs_self, h.2.1]
  have e := exec_jal (σ.set .nextPC (σ.regs .PC + 4)) (sys_set h.1 .nextPC _ rfl) rd x (by rw [hp]; exact hT)
  rw [hp, hn] at e
  exact step_jump h ha h2 _ hdec rd _ _ hT e

theorem kind_jalr (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (rd rs1 : BitVec 5) (x : BitVec 12)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.jalr rd rs1 (x.signExtend 32)))
    (ht : RV.exec s (.jalr rd rs1 (x.signExtend 32)) = some t) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree t σ' := by
  simp only [RV.exec, RV.State.goto] at ht
  split_ifs at ht with hT
  case neg => simp at ht
  simp only [Option.map_some, Option.some.injEq] at ht; subst ht
  have hx : xget (σ.set .nextPC (σ.regs .PC + 4)) rs1 = s.getReg rs1 := by rw [xget_set_nextPC, agree_xget h]
  have hn : (σ.set .nextPC (σ.regs .PC + 4)).regs .nextPC = s.pc + 4 := by rw [set_regs_self, h.2.1]
  have e := exec_jalr (σ.set .nextPC (σ.regs .PC + 4)) (sys_set h.1 .nextPC _ rfl) rd rs1 x (by rw [hx]; exact hT)
  rw [hx, hn] at e
  exact step_jump h ha h2 _ hdec rd _ _ hT e

theorem kind_branch (h : Airbender.Agree s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (c : RV.Cond) (rs1 rs2 : BitVec 5) (x : BitVec 13)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.branch c rs1 rs2 (x.signExtend 32)))
    (ht : RV.exec s (.branch c rs1 rs2 (x.signExtend 32)) = some t) :
    ∃ σ', Airbender.step σ = some σ' ∧ Airbender.Agree t σ' := by
  have hp := set1_PC σ (σ.regs .PC + 4) h.2.1
  have h1 : xget (σ.set .nextPC (σ.regs .PC + 4)) rs1 = s.getReg rs1 := by rw [xget_set_nextPC, agree_xget h]
  have h2' : xget (σ.set .nextPC (σ.regs .PC + 4)) rs2 = s.getReg rs2 := by rw [xget_set_nextPC, agree_xget h]
  simp only [RV.exec, RV.State.goto] at ht
  by_cases hc : c.holds (s.getReg rs1) (s.getReg rs2) = true
  · simp only [hc, ↓reduceIte] at ht
    split_ifs at ht with hT
    simp only [Option.some.injEq] at ht; subst ht
    have e := exec_branch (σ.set .nextPC (σ.regs .PC + 4)) (sys_set h.1 .nextPC _ rfl) c rs1 rs2 x
      (by rw [h1, h2', hp]; intro; exact hT)
    rw [h1, h2', hp] at e; simp only [hc, ↓reduceIte] at e
    exact step_goto h ha h2 _ hdec _ hT e
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at ht; subst ht
    have e := exec_branch (σ.set .nextPC (σ.regs .PC + 4)) (sys_set h.1 .nextPC _ rfl) c rs1 rs2 x
      (by rw [h1, h2']; intro hc'; exact absurd hc' hc)
    rw [h1, h2'] at e; simp only [hc, Bool.false_eq_true, ↓reduceIte] at e
    exact step_next h ha h2 _ hdec e

end Slop.Equiv
