import Slop.Equiv.StepMem
import Slop.Equiv.StepMop

/-! `Airbender.StepIsAirbender`: one step of our spec is one step of the Airbender machine. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

theorem step_is_airbender : Airbender.StepIsAirbender := by
  intro s t σ h ht
  unfold RV.step at ht
  split_ifs at ht with hc
  obtain ⟨ha, hrom⟩ := hc
  have hpcs : σ.regs .PC = s.pc := h.2.1
  have h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START := by rw [hpcs]; exact hrom
  have ha' : (σ.regs .PC).toNat % 4 = 0 := by rw [hpcs]; exact ha
  have hrd : RV.read s.mem s.pc 4 = readBytes σ.mem (σ.regs .PC).toNat 4 := by
    rw [hpcs, read_eq4 σ.mem s.mem h.2.2.2 _ (by simp only [RV.ROM_END] at hrom; omega), BitVec.setWidth_eq]
  rw [hrd] at ht
  obtain ⟨i, hdec, hex⟩ := Option.bind_eq_some_iff.mp ht
  have hd := hdec
  unfold RV.decode at hd
  simp only at hd
  split at hd <;> cases hd
  all_goals first
    | exact kind_lui h ha' h2 _ _ hdec hex
    | exact kind_auipc h ha' h2 _ _ hdec hex
    | exact kind_jal h ha' h2 _ _ hdec hex
    | exact kind_jalr h ha' h2 _ _ _ hdec hex
    | exact kind_branch h ha' h2 _ _ _ _ hdec hex
    | exact kind_load h ha' h2 _ _ (by simp) _ _ _ hdec hex
    | exact kind_store h ha' h2 _ (by simp) _ _ _ hdec hex
    | exact kind_itype h ha' h2 _ _ _ _ (by simp) hdec hex
    | exact kind_shift h ha' h2 _ _ _ _ (by simp) hdec hex
    | exact kind_op h ha' h2 _ _ _ _ (by simp) hdec hex
    | exact kind_mop h ha' h2 _ _ _ _ hdec hex

end Slop.Equiv
