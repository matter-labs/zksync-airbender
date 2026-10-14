import Slop.Equiv.StepIsAirbender
import Slop.RV.Final
import HumanSail.Theorems

/-! `Airbender.ProgramCorrect`: the final theorem, carried from our spec to the Airbender machine. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

/-- Runs of our spec are runs of the Airbender machine. -/
theorem run_agree : ∀ (n : Nat) (s s' : RV.State) (σ : FState), Airbender.Agree s σ → RV.run n s = some s' →
    ∃ σ', Airbender.run n σ = some σ' ∧ Airbender.Agree s' σ'
  | 0, s, s', σ, h, hr => by
    simp only [RV.run, Option.some.injEq] at hr; subst hr; exact ⟨σ, rfl, h⟩
  | n + 1, s, s', σ, h, hr => by
    obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨σ1, hσ1, h1⟩ := step_is_airbender s t σ h ht
    obtain ⟨σ', hσ', h'⟩ := run_agree n t s' σ1 h1 hr
    exact ⟨σ', by simp only [Airbender.run, hσ1, Option.bind_some, hσ'], h'⟩

/-- Our view of an Airbender state. -/
noncomputable def ofSail (σ : FState) : RV.State :=
  { pc := σ.regs .PC, regFile := fun i => Airbender.reg σ i, mem := fun a => σ.mem a.toNat }

theorem agree_ofSail (σ : FState) (hs : Airbender.Sys σ) : Airbender.Agree (ofSail σ) σ := by
  refine ⟨hs, rfl, ?_, fun _ => rfl⟩
  intro i
  simp only [RV.State.getReg, ofSail]
  split_ifs with h
  · subst h; rw [reg_eq, xget_zero]
  · rfl

theorem program_correct_airbender : Airbender.ProgramCorrect := by
  intro σ x hs hpc himg hin hx
  have hA := agree_ofSail σ hs
  have himg' : RV.ImageLoaded (ofSail σ) := by
    intro i hi
    have hb : Image.bytes.size < 2 ^ 32 := by decide +kernel
    show σ.mem (BitVec.ofNat 32 i).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact himg i hi
  have hin' : RV.read (ofSail σ).mem (BitVec.ofNat 32 Image.INPUT) 4 = x := by
    rw [read_eq4 σ.mem (ofSail σ).mem (fun _ => rfl) _ (by decide), BitVec.setWidth_eq]
    have e : (BitVec.ofNat 32 Image.INPUT).toNat = Image.INPUT := by decide
    rw [e]; exact hin
  obtain ⟨n, s', hr, hpc', h10, h11a, h11b, hk⟩ := RV.program_correct (ofSail σ) x hpc himg' hin' hx
  obtain ⟨σ', hσ', hA'⟩ := run_agree n _ s' σ hA hr
  have hreg : ∀ i, Airbender.reg σ' i = s'.getReg i := hA'.2.2.1
  refine ⟨n, σ', hσ', hA'.2.1.trans hpc', (hreg 10).trans h10, ?_, ?_, ?_⟩
  · rw [hreg]; exact h11a
  · rw [hreg]; exact h11b
  · intro k
    obtain ⟨s'', hr'', hpc'', hreg''⟩ := hk k
    obtain ⟨σ'', hσ'', hA''⟩ := run_agree k s' s'' σ' hA' hr''
    refine ⟨σ'', hσ'', ?_, ?_⟩
    · rw [hA''.2.1, hA'.2.1, hpc'']
    · intro i; rw [hA''.2.2.1, hreg, hreg'']

end Slop.Equiv
