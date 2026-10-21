import Airbender.Review.Helpers.Context.SubwordMemory
import Airbender.Proofs.Trace.MemoryHistory
import Airbender.Proofs.Trace.PublicImage
import Airbender.Proofs.SubwordMemory.Timestamp

namespace Airbender.Trace.Proofs
set_option autoImplicit false

/-- The v2 subword-memory artifact discharges the existing shared clock contract.
    No per-row bound, alignment or prior-clock premise is introduced. -/
instance {p : Nat} [Fact p.Prime] : ClockLaws SubwordMemoryFamily p where
  finalBound rom row h := by
    cases row with
    | mk family w =>
      cases family
      exact SubwordMemory.Proofs.final_clock_bound h
  advance hp rom row h bound := by
    cases row with
    | mk family w =>
      cases family
      exact SubwordMemory.Proofs.clock_advance hp h bound
  portsClocks row := by
    cases row with
    | mk family w => cases family; exact SubwordMemory.Proofs.memory_clocks
  offsets row := by
    cases row with
    | mk family w => cases family; rfl
  effects hp rom row h inputs := by
    cases row with
    | mk family w =>
      cases family
      exact SubwordMemory.Proofs.clock_effects hp h inputs

end Airbender.Trace.Proofs
