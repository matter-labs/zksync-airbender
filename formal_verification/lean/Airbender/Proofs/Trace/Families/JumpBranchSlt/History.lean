import Airbender.Review.Helpers.Context.JumpBranchSlt
import Airbender.Proofs.Trace.MemoryHistory
import Airbender.Proofs.Trace.PublicImage
import Airbender.Proofs.JumpBranchSlt.Timestamp

namespace Airbender.Trace.Proofs

/-- The v2 control artifact discharges the existing shared clock contract.
    No per-row bound, alignment or prior-clock premise is introduced. -/
instance [Fact p.Prime] : ClockLaws JumpBranchSltFamily p where
  finalBound rom row h := by
    cases row with
    | mk family w =>
      cases family
      exact JumpBranchSlt.Proofs.final_clock_bound h
  advance hp rom row h bound := by
    cases row with
    | mk family w =>
      cases family
      exact JumpBranchSlt.Proofs.clock_advance hp h bound
  portsClocks row := by
    cases row with
    | mk family w => cases family; exact JumpBranchSlt.Proofs.memory_clocks
  offsets row := by
    cases row with
    | mk family w => cases family; rfl
  effects hp rom row h inputs := by
    cases row with
    | mk family w =>
      cases family
      exact JumpBranchSlt.Proofs.clock_effects hp h inputs

end Airbender.Trace.Proofs
