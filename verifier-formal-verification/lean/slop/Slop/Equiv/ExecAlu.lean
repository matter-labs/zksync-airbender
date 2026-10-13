import Slop.Equiv.Alu

/-! Sail's `execute` on our ALU instructions (in Sail's names, `toSail`): the result is our `RV.alu` value
written to `rd`. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv

theorem exec_rtype (σ : FState) (rs2 rs1 rd : BitVec 5) (o : RV.Op)
    (ho : o = .add ∨ o = .sub ∨ o = .sll ∨ o = .slt ∨ o = .sltu ∨ o = .xor ∨ o = .srl ∨ o = .sra ∨ o = .or ∨ o = .and) :
    runF (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) (Airbender.sailRop o)) σ =
      .ok RETIRE_SUCCESS (xset σ rd (RV.alu o (xget σ rs1) (xget σ rs2))) := by
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [execute_RTYPE, Airbender.sailRop, Slop.runF_bind, rX_run, wX_run, Slop.runF_pure, RV.alu,
    sll_eq, srl_eq, sra_eq, slt_eq, sltu_eq]

theorem sext12 (x : BitVec 12) : sign_extend (m := 32) ((x.signExtend 32).extractLsb' 0 12) = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend, BitVec.getLsbD_extractLsb']
  by_cases h : j < 12 <;> simp [h, hj, BitVec.msb_eq_getLsbD_last, BitVec.getMsbD_eq_getLsbD, BitVec.getElem_signExtend]

theorem exec_itype (σ : FState) (rs1 rd : BitVec 5) (x : BitVec 12) (o : RV.Op)
    (ho : o = .add ∨ o = .slt ∨ o = .sltu ∨ o = .xor ∨ o = .or ∨ o = .and) :
    runF (Airbender.execute (Airbender.toSail (.opImm o rd rs1 (x.signExtend 32)))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (RV.alu o (xget σ rs1) (x.signExtend 32))) := by
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Airbender.toSail, Airbender.execute, execute, execute_ITYPE, Slop.runF_bind, rX_run, wX_run,
    Slop.runF_pure, RV.alu, sext12, slt_eq, sltu_eq]

theorem exec_op_alu (σ : FState) (rs2 rs1 rd : BitVec 5) (o : RV.Op)
    (ho : o = .add ∨ o = .sub ∨ o = .sll ∨ o = .slt ∨ o = .sltu ∨ o = .xor ∨ o = .srl ∨ o = .sra ∨ o = .or ∨ o = .and) :
    runF (Airbender.execute (Airbender.toSail (.op o rd rs1 rs2))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (RV.alu o (xget σ rs1) (xget σ rs2))) := by
  rw [← exec_rtype σ rs2 rs1 rd o ho]
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem exec_shiftiop (σ : FState) (rs1 rd sh : BitVec 5) (o : RV.Op) (ho : o = .sll ∨ o = .srl ∨ o = .sra) :
    runF (Airbender.execute (Airbender.toSail (.opImm o rd rs1 (sh.zeroExtend 32)))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (RV.alu o (xget σ rs1) (sh.zeroExtend 32))) := by
  rcases ho with rfl | rfl | rfl <;>
  simp only [Airbender.toSail, Airbender.execute, execute, execute_SHIFTIOP, Slop.runF_bind, rX_run, wX_run,
    Slop.runF_pure, RV.alu, sll6_eq, srl6_eq, sra6_eq]

end Slop.Equiv
