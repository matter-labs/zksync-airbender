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

theorem exec_mext (σ : FState) (rs2 rs1 rd : BitVec 5) (o : RV.Op) (ho : o = .mul ∨ o = .mulhu ∨ o = .divu ∨ o = .remu) :
    runF (Airbender.execute (Airbender.toSail (.op o rd rs1 rs2))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (RV.alu o (xget σ rs1) (xget σ rs2))) := by
  rcases ho with rfl | rfl | rfl | rfl <;>
  simp only [Airbender.toSail, Airbender.execute, execute, execute_MUL, execute_DIV, execute_REM, Slop.runF_bind,
    rX_run, Slop.runF_pure, RV.alu, mult_to_bits_half, Functions.xlen, ite_true, SailRV32.not,
    Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false] <;> simp only [wX_run, Slop.runF_pure] <;>
  congr 2 <;> apply BitVec.eq_of_toNat_eq <;>
  simp [to_bits_truncate, get_slice_int, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.toNatInt,
    mul_int, mulhu_nat, divu_nat, remu_nat]

theorem upper_eq (u : BitVec 20) :
    sign_extend (m := 32) ((u ++ (0 : BitVec 12)).extractLsb' 12 20 ++ 0x000#12) = u ++ (0 : BitVec 12) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h : j < 12
  · simp [h]
  · simp only [h, ↓reduceIte, BitVec.getLsbD_extractLsb']
    rw [show 12 + (j - 12) = j by omega, BitVec.getLsbD_append]
    simp [h, show j - 12 < 20 by omega]

theorem exec_lui (σ : FState) (rd : BitVec 5) (u : BitVec 20) :
    runF (Airbender.execute (Airbender.toSail (.lui rd (u ++ (0 : BitVec 12))))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (u ++ (0 : BitVec 12))) := by
  simp only [Airbender.toSail, Airbender.execute, execute, execute_UTYPE, Slop.runF_bind, Slop.runF_pure,
    upper_eq, wX_run]

theorem exec_auipc (σ : FState) (rd : BitVec 5) (u : BitVec 20) :
    runF (Airbender.execute (Airbender.toSail (.auipc rd (u ++ (0 : BitVec 12))))) σ =
      .ok RETIRE_SUCCESS (xset σ rd (σ.regs .PC + (u ++ (0 : BitVec 12)))) := by
  simp only [Airbender.toSail, Airbender.execute, execute, execute_UTYPE, Slop.runF_bind, Slop.runF_pure,
    upper_eq, wX_run, get_arch_pc]
  rw [Slop.runF_readReg]

end Slop.Equiv
