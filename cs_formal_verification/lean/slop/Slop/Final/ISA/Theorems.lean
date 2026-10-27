import Slop.ISA.Equiv.Decode
import Slop.ISA.Equiv.StepIsAirbender
import Slop.ISA.Equiv.Checks

namespace Airbender

/-- 1. Sail decodes every word of our table to the same instruction (on any Airbender state). -/
theorem decode_is_sail : DecodeIsSailClaim := Slop.Equiv.decode_is_sail

/-- 2. One step of our spec is one step of the Airbender machine. -/
theorem step_is_airbender : StepIsAirbenderClaim := Slop.Equiv.step_is_airbender

/-- The circuit claims' `Configured` gives `Configured` on the Sail state it views. -/
theorem configured_bridge : ConfiguredBridgeClaim := by
  intro state configured r outside
  simp only [Airbender.Reference.RiscV.Sail.Configuration.SailState.ofState, configured r outside, Option.getD_some]

/-- The machine checks. -/
theorem machine_checks_claim : MachineChecksClaim := machine_checks

end Airbender
