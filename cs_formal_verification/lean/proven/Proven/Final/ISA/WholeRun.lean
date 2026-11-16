import Proven.ISA.Equiv.WholeRun

namespace Airbender

theorem run_is_airbender : RunIsAirbenderClaim := Proven.Equiv.run_is_airbender

theorem agree_exists : AgreeExistsClaim := Proven.Equiv.agree_exists

theorem fetch_keeps_configured : FetchKeepsConfiguredClaim := Proven.Equiv.fetch_keeps_configured

theorem run_is_airbender_satisfiable : RunIsAirbenderSatisfiableClaim := by
  obtain ⟨state, after, machine, agreement, step⟩ := Proven.Equiv.NonVacuous.step_assumptions
  exact ⟨1, state, after, machine, by decide, agreement,
    by simp only [RV.run, step, Option.bind_some]⟩

theorem agree_exists_satisfiable : AgreeExistsSatisfiableClaim := by
  obtain ⟨machine, agreement⟩ := agree_exists Proven.Equiv.NonVacuous.state
  exact ⟨_, machine, agreement⟩

theorem fetch_keeps_configured_satisfiable : FetchKeepsConfiguredSatisfiableClaim := by
  refine ⟨Proven.Equiv.NonVacuous.sail, 0x00000013#32, _, .F_Base 0x00000013#32,
    Proven.Equiv.NonVacuous.sail, Proven.Equiv.NonVacuous.configured,
    by decide +kernel, by decide +kernel, ?_, (Option.some_get (by decide)).symm, ?_⟩
  · decide +kernel
  · exact Proven.Equiv.fetch_rom _ Proven.Equiv.NonVacuous.configured
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Airbender
