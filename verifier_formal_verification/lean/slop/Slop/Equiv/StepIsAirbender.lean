import Slop.Equiv.StepMem
import Slop.Equiv.StepMop
import Slop.Equiv.StepInput

/-! `Airbender.StepIsAirbender`: one step of our spec is one step of the Airbender machine. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

/-- On Sail's state: our step is a step of the machine fed the next input word. -/
theorem step_sail (s t : RV.State) (σ : SailState) (h : Airbender.AgreeSail s σ) (ht : RV.step s = some t) :
    ∃ σ' r, stepSail (s.input s.inputPos) σ = some (σ', r) ∧ Airbender.AgreeSail t σ' ∧ t.input = s.input ∧
      t.inputPos = if r then s.inputPos + 1 else s.inputPos := by
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
  cases hr : Airbender.readsInput i
  · obtain ⟨hi, hp⟩ := exec_keeps_input hex hr
    suffices ∃ σ', stepSail (s.input s.inputPos) σ = some (σ', false) ∧ Airbender.AgreeSail t σ' by
      obtain ⟨σ', e, a⟩ := this; exact ⟨σ', false, e, a, hi, hp⟩
    have hd := hdec
    unfold RV.decode at hd
    simp only at hd
    split at hd <;> (try split_ifs at hd) <;> cases hd
    all_goals first
      | (simp [Airbender.readsInput] at hr; done)
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
  · obtain ⟨rd, rfl⟩ : ∃ rd, i = .inputRead rd := by cases i <;> simp_all [Airbender.readsInput]
    have hrd0 : rd ≠ 0 := by
      have hd := hdec
      unfold RV.decode at hd
      simp only at hd
      split at hd <;> (try split_ifs at hd with hh) <;> cases hd
      exact hh.2.2
    simp only [RV.exec, Option.some.injEq] at hex; subst hex
    obtain ⟨σ', e, a⟩ := kind_input (next := s.input s.inputPos) h ha' h2 rd hdec hrd0
    exact ⟨σ', true, e, a, rfl, rfl⟩

theorem step_is_airbender : Airbender.StepIsAirbender := by
  intro s t m ⟨hA, hin, hpos⟩ ht
  obtain ⟨σ', r, e, a, h3, h4⟩ := step_sail s t m.sail hA ht
  refine ⟨⟨σ', m.input, if r then m.inputPos + 1 else m.inputPos⟩, ?_, a, ?_, ?_⟩
  · rw [step_eq, show m.input m.inputPos = s.input s.inputPos by rw [hin, hpos], e]; rfl
  · show m.input = t.input; rw [h3, hin]
  · show (if r then m.inputPos + 1 else m.inputPos) = t.inputPos; rw [h4, hpos]

end Slop.Equiv
