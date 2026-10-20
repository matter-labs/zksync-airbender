import Slop.Equiv.StepMem
import Slop.Equiv.StepMop
import Slop.Equiv.StepInput
import Slop.Equiv.StepDelegate

/-! `Airbender.StepIsAirbender`: one step of our spec is one step of the Airbender machine. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

/-- On Sail's state: our step is a step of the machine fed the next input word. -/
theorem step_sail (s t : RV.State) (σ : SailState) (h : Airbender.AgreeSail s σ) (ht : RV.step s = some t)
    (hnd : ∀ k, RV.decode (RV.read s.mem s.pc 4) ≠ some (.delegate k)) :
    ∃ σ' r, stepSail (s.input.headD 0) σ = some (σ', r) ∧ Airbender.AgreeSail t σ' ∧
      if r then ∃ w, s.input = w :: t.input else t.input = s.input := by
  unfold RV.step at ht
  split_ifs at ht with hc
  obtain ⟨ha, hrom⟩ := hc
  have hpcs : σ.regs .PC = s.pc := h.2.1
  have h2 : (σ.regs .PC).toNat + 4 ≤ Airbender.RAM_START := by rw [hpcs]; exact hrom
  have ha' : (σ.regs .PC).toNat % 4 = 0 := by rw [hpcs]; exact ha
  have hrd : RV.read s.mem s.pc 4 = readBytes σ.mem (σ.regs .PC).toNat 4 := by
    rw [hpcs, read_eq4 σ.mem s.mem h.2.2.2 _ (by simp only [RV.ROM_END] at hrom; omega), BitVec.setWidth_eq]
  rw [hrd] at ht hnd
  obtain ⟨i, hdec, hex⟩ := Option.bind_eq_some_iff.mp ht
  cases hr : RV.Instr.readsInput i
  · have hi := RV.exec_keeps_input hex hr
    suffices ∃ σ', stepSail (s.input.headD 0) σ = some (σ', false) ∧ Airbender.AgreeSail t σ' by
      obtain ⟨σ', e, a⟩ := this; exact ⟨σ', false, e, a, hi⟩
    have hd := hdec
    unfold RV.decode at hd
    simp only at hd
    split at hd <;> (try simp only [RV.decodeCsr] at hd) <;> (try split_ifs at hd) <;>
      first | cases hd | obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hd
    all_goals first
      | (simp [RV.Instr.readsInput] at hr; done)
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
      | exact kind_write h ha' h2 _ hdec hex
      | exact absurd hdec (hnd _)
  · obtain ⟨rd, rfl⟩ : ∃ rd, i = .inputRead rd := by cases i <;> simp_all [RV.Instr.readsInput]
    simp only [RV.exec] at hex
    rcases hs : s.input with _ | ⟨w, rest⟩ <;> rw [hs] at hex
    · cases hex
    simp only [Option.some.injEq] at hex; subst hex
    obtain ⟨σ', e, a⟩ := kind_input (next := s.input.headD 0) h ha' h2 rd hdec
    rw [hs] at e a
    exact ⟨σ', true, e, a, w, rfl⟩

theorem step_is_airbender : Airbender.StepIsAirbender := by
  intro s t m ⟨hA, hin⟩ ht
  have ht' := ht
  unfold RV.step at ht'
  split_ifs at ht' with hc
  obtain ⟨i, hdec, hex⟩ := Option.bind_eq_some_iff.mp ht'
  by_cases hd : ∃ k, i = .delegate k
  · -- a delegation call: our definition on both sides
    obtain ⟨k, rfl⟩ := hd
    obtain ⟨σ', e, a⟩ := kind_delegate hA k hc hdec hex
    refine ⟨⟨σ', m.input⟩, ?_, a, ?_⟩
    · unfold Airbender.step; rw [e]; rfl
    · show m.input = t.input; rw [hin]; exact (RV.exec_keeps_input hex rfl).symm
  have hnd : ∀ k, RV.decode (RV.read s.mem s.pc 4) ≠ some (.delegate k) := fun k h =>
    hd ⟨k, Option.some.inj (hdec.symm.trans h)⟩
  have hnone := delegation_none hA hdec (fun k h => hd ⟨k, h⟩)
  rw [show m.sail = m.sail from rfl] at hnone
  obtain ⟨σ', r, e, a, hr⟩ := step_sail s t m.sail hA ht hnd
  rw [← hin] at e hr
  rw [step_eq m σ' r hnone e]
  cases r
  · exact ⟨_, rfl, a, by simp only at hr ⊢; rw [hr, hin]⟩
  · obtain ⟨w, hw⟩ := hr
    simp only [hw]
    exact ⟨_, rfl, a, rfl⟩

end Slop.Equiv
