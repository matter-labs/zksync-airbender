import Airbender.Review.Helpers.UnifiedReduced
import Airbender.Proofs.UnifiedReduced.ArtifactChecks
import Airbender.Proofs.UnifiedReduced.Timestamp
import Airbender.Proofs.Trace.History

namespace Airbender.UnifiedReduced.Proofs
open Trace

instance unifiedClockLaws {p : Nat} [Fact p.Prime] : Trace.Proofs.ClockLaws UnifiedFamily p where
  finalBound _ _ h := final_clock_bound h
  advance hp inverse _ _ h bound := clock_advance hp inverse h bound
  portsClocks _ := memory_clocks
  offsets _ := rfl
  effects hp inverse _ _ h inputs := clocks hp inverse h inputs

end Airbender.UnifiedReduced.Proofs
