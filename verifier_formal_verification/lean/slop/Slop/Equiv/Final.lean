import Slop.Equiv.StepIsAirbender
import Slop.RV.FinalMop
import Slop.RV.FinalPlain
import HumanSail.Theorems

/-! `Airbender.ProgramCorrect`: the final theorem, carried from our spec to the Airbender machine. -/

open Sail SailRV32 SailRV32.Functions Human

namespace Slop.Equiv
set_option maxHeartbeats 0

/-- Runs of our spec are runs of the Airbender machine. -/
theorem run_agree : ∀ (n : Nat) (s s' : RV.State) (σ : Airbender.Machine), Airbender.Agree s σ →
    RV.run n s = some s' → ∃ σ', Airbender.run n σ = some σ' ∧ Airbender.Agree s' σ'
  | 0, s, s', σ, h, hr => by
    simp only [RV.run, Option.some.injEq] at hr; subst hr; exact ⟨σ, rfl, h⟩
  | n + 1, s, s', σ, h, hr => by
    obtain ⟨t, ht, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨σ1, hσ1, h1⟩ := step_is_airbender s t σ h ht
    obtain ⟨σ', hσ', h'⟩ := run_agree n t s' σ1 h1 hr
    exact ⟨σ', by simp only [Airbender.run, hσ1, Option.bind_some, hσ'], h'⟩

/-- Our view of an Airbender state. -/
noncomputable def ofSail (σ : SailState) (input : List RV.Word) : RV.State :=
  { pc := σ.regs .PC, regFile := fun i => Airbender.getReg σ i, mem := fun a => σ.mem a.toNat, input }

theorem agree_ofSail (σ : SailState) (input : List RV.Word) (hs : Airbender.Configured σ) :
    Airbender.Agree (ofSail σ input) ⟨σ, input⟩ := by
  refine ⟨⟨hs, rfl, ?_, fun _ => rfl⟩, rfl⟩
  intro i
  simp only [RV.State.getReg, ofSail]
  split_ifs with h
  · subst h; rw [reg_eq, xget_zero]
  · rfl

/-- The final theorem on our spec gives it on the Airbender machine, for any image. -/
theorem program_correct_of (bytes : Array (BitVec 8)) (halt : Nat) (hb : bytes.size < 2 ^ 32)
    (h : RV.ProgramCorrectOf bytes halt) : Airbender.ProgramCorrectOf bytes halt := by
  intro σ x y0 y1 y2 y3 rest hs hpc himg hram hxP hy0p hy1p hy2p hy3p
  have hA := agree_ofSail σ (x :: y0 :: y1 :: y2 :: y3 :: rest) hs
  have himg' : RV.ImageLoaded bytes (ofSail σ (x :: y0 :: y1 :: y2 :: y3 :: rest)) := by
    intro i hi
    show σ.mem (BitVec.ofNat 32 i).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact himg i hi
  have hram' : RV.RamZero (ofSail σ (x :: y0 :: y1 :: y2 :: y3 :: rest)) := fun addr h1 h2 => hram addr.toNat h1 h2
  obtain ⟨n, s', hr, hpc', h10, h11a, h11b, hlt, hlimbs, h16, h17, hz, hk⟩ := h _ x y0 y1 y2 y3 rest hpc himg'
    hram' rfl hxP hy0p hy1p hy2p hy3p
  obtain ⟨σ', hσ', hA'⟩ := run_agree n _ s' _ hA hr
  have hreg : ∀ i, Airbender.getReg σ'.sail i = s'.getReg i := hA'.1.2.2.1
  refine ⟨n, σ', hσ', hA'.1.2.1.trans hpc', (hreg 10).trans h10, ?_, ?_, ?_, ?_, (hreg 16).trans h16,
    (hreg 17).trans h17, ?_, ?_⟩
  · rw [hreg]; exact h11a
  · rw [hreg]; exact h11b
  · intro i h1 h2; rw [hreg]; exact hlt i h1 h2
  · simp only [hreg]; exact hlimbs
  · intro i h1 h2; rw [hreg]; exact hz i h1 h2
  · intro k
    obtain ⟨s'', hr'', hpc'', hreg''⟩ := hk k
    obtain ⟨σ'', hσ'', hA''⟩ := run_agree k s' s'' σ' hA' hr''
    refine ⟨σ'', hσ'', ?_, ?_⟩
    · rw [hA''.1.2.1, hA'.1.2.1, hpc'']
    · intro i; rw [hA''.1.2.2.1, hreg, hreg'']

/-- `Airbender.ProgramCorrect`: the plain-Rust image on the Airbender machine. -/
theorem program_correct_airbender : Airbender.ProgramCorrect :=
  program_correct_of _ _ (by decide +kernel) RV.program_correct

/-- `Airbender.ProgramCorrectMop`: the field-opcode image on the Airbender machine. -/
theorem program_correct_airbender_mop : Airbender.ProgramCorrectMop :=
  program_correct_of _ _ (by decide +kernel) RV.program_correct_mop

end Slop.Equiv
