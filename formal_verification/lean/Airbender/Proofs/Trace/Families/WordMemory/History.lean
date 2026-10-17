import Airbender.Review.Helpers.Context.WordMemory
import Airbender.Proofs.Trace.MemoryHistory
import Airbender.Proofs.Trace.PublicImage
import Airbender.Proofs.WordMemory.Timestamp

namespace Airbender.Trace.Proofs

/-- The v2 word-memory artifact discharges the existing shared clock contract.
    No per-row bound, alignment or prior-clock premise is introduced. -/
instance [Fact p.Prime] : ClockLaws WordMemoryFamily p where
  finalBound rom row h := by
    cases row with
    | mk family w =>
      cases family
      exact WordMemory.Proofs.final_clock_bound h
  advance hp rom row h bound := by
    cases row with
    | mk family w =>
      cases family
      exact WordMemory.Proofs.clock_advance hp h bound
  portsClocks row := by
    cases row with
    | mk family w => cases family; exact WordMemory.Proofs.memory_clocks
  offsets row := by
    cases row with
    | mk family w => cases family; rfl
  effects hp rom row h inputs := by
    cases row with
    | mk family w =>
      cases family
      exact WordMemory.Proofs.clock_effects hp h inputs

end Airbender.Trace.Proofs
