module
public import Human.Helpers.UnifiedReduced.Registry
public import Slop.UnifiedReduced.ArtifactChecks
public import Slop.UnifiedReduced.Timestamp
public import Slop.Trace.History
public import Slop.Defs.Helpers.Context.Columns

@[expose] public section

namespace Airbender.UnifiedReduced.Proofs
open Trace

instance unifiedClockLaws {p : Nat} [Fact p.Prime] : Trace.Proofs.ClockLaws UnifiedFamily p where
  finalBound _ _ h := final_clock_bound h
  advance hp inverse _ _ h bound := clock_advance hp inverse h bound
  portsClocks _ := memory_clocks
  offsets _ := rfl
  effects hp inverse _ _ h inputs := clocks hp inverse h inputs

end Airbender.UnifiedReduced.Proofs
