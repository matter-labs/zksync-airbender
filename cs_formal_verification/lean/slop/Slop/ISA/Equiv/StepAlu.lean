import Slop.ISA.Equiv.Agree

/-! Our step = an Airbender step, for LUI, AUIPC, OP-IMM and OP (incl. the M extension). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 400000

variable {s t : RV.State} {σ : SailState} {next : BitVec 32}

theorem kind_lui (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (rd : BitVec 5) (u : BitVec 20)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.lui rd (u ++ (0 : BitVec 12))))
    (ht : RV.exec s (.lui rd (u ++ (0 : BitVec 12))) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec, Option.some.injEq] at ht; subst ht
  exact step_write h ha h2 _ hdec rd _ (exec_lui _ rd u)

theorem kind_auipc (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (rd : BitVec 5) (u : BitVec 20)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.auipc rd (u ++ (0 : BitVec 12))))
    (ht : RV.exec s (.auipc rd (u ++ (0 : BitVec 12))) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec, Option.some.injEq] at ht; subst ht
  have e := exec_auipc (next := next) (σ.set .nextPC (σ.regs .PC + 4)) rd u
  have hp : (σ.set .nextPC (σ.regs .PC + 4)).regs .PC = s.pc := by
    rw [set_regs_ne _ _ _ _ (by decide)]; exact h.2.1
  rw [hp] at e
  exact step_write h ha h2 _ hdec rd _ e

theorem kind_itype (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (o : RV.Op) (rd rs1 : BitVec 5) (x : BitVec 12)
    (ho : o = .add ∨ o = .slt ∨ o = .sltu ∨ o = .xor ∨ o = .or ∨ o = .and)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.opImm o rd rs1 (x.signExtend 32)))
    (ht : RV.exec s (.opImm o rd rs1 (x.signExtend 32)) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec, Option.some.injEq] at ht; subst ht
  have e := exec_itype (next := next) (σ.set .nextPC (σ.regs .PC + 4)) rs1 rd x o ho
  rw [xget_set_nextPC, agree_xget h] at e
  exact step_write h ha h2 _ hdec rd _ e

theorem kind_shift (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (o : RV.Op) (rd rs1 sh : BitVec 5)
    (ho : o = .sll ∨ o = .srl ∨ o = .sra)
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.opImm o rd rs1 (sh.zeroExtend 32)))
    (ht : RV.exec s (.opImm o rd rs1 (sh.zeroExtend 32)) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec, Option.some.injEq] at ht; subst ht
  have e := exec_shiftiop (next := next) (σ.set .nextPC (σ.regs .PC + 4)) rs1 rd sh o ho
  rw [xget_set_nextPC, agree_xget h] at e
  exact step_write h ha h2 _ hdec rd _ e

theorem kind_op (h : Airbender.AgreeSail s σ) (ha : (σ.regs .PC).toNat % 4 = 0)
    (h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START) (o : RV.Op) (rd rs1 rs2 : BitVec 5)
    (ho : (o = .add ∨ o = .sub ∨ o = .sll ∨ o = .slt ∨ o = .sltu ∨ o = .xor ∨ o = .srl ∨ o = .sra ∨ o = .or ∨
      o = .and) ∨ (o = .mul ∨ o = .mulhu ∨ o = .divu ∨ o = .remu))
    (hdec : RV.decode (readBytes σ.mem (σ.regs .PC).toNat 4) = some (.op o rd rs1 rs2))
    (ht : RV.exec s (.op o rd rs1 rs2) = some t) :
    ∃ σ', stepSail next σ = some (σ', false) ∧ Airbender.AgreeSail t σ' := by
  simp only [RV.exec, Option.some.injEq] at ht; subst ht
  have e : runSail (Airbender.execute next (Airbender.toSail (.op o rd rs1 rs2))) (σ.set .nextPC (σ.regs .PC + 4)) =
      .ok RETIRE_SUCCESS (xset (σ.set .nextPC (σ.regs .PC + 4)) rd
        (RV.alu o (xget (σ.set .nextPC (σ.regs .PC + 4)) rs1) (xget (σ.set .nextPC (σ.regs .PC + 4)) rs2))) := by
    rcases ho with ho | ho
    · exact exec_op_alu _ rs2 rs1 rd o ho
    · exact exec_mext _ rs2 rs1 rd o ho
  rw [xget_set_nextPC, xget_set_nextPC, agree_xget h, agree_xget h] at e
  exact step_write h ha h2 _ hdec rd _ e

end Slop.Equiv
