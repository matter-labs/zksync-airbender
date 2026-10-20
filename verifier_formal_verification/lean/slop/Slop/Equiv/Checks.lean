import HumanSail.Checks

/-! `Airbender.MachineChecks`: each conjunct evaluated by the Lean kernel on the Sail model. -/

namespace Airbender

theorem machine_checks : MachineChecks := by
  unfold MachineChecks
  and_intros <;> decide +kernel

end Airbender
