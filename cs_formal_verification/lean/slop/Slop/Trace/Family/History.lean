import Slop.Trace.Family.Timestamps
import Slop.Trace.History
import Slop.AddSub.ArtifactChecks
import Slop.Trace.Rows
import Slop.WordMemory.ArtifactChecks
import Human.Helpers.Context.FamilyLayout

namespace Airbender.Trace.Proofs

instance [Fact p.Prime] : ClockLaws Family p where
  finalBound rom row h := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact addSub_final_bound h
      | wordMemory => exact wordMemory_final_bound rom h
  advance hp inverse rom row h bound := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact (addSub_step hp inverse h bound).2
      | wordMemory => exact (wordMemory_step hp inverse rom h bound).2
  portsClocks row := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact AddSub.memory_clocks
      | wordMemory => exact WordMemory.memory_clocks
  offsets row := by
    cases row with
    | mk family w => cases family <;> rfl
  effects hp inverse rom row h inputs := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact addSub_clock hp inverse h inputs
      | wordMemory => exact wordMemory_clock hp inverse rom h inputs

end Airbender.Trace.Proofs
