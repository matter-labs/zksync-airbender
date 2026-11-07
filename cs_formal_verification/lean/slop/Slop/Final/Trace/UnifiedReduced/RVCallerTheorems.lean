import Human.Trace.UnifiedReduced.RVCallerTheorems
import Slop.UnifiedReduced.RVCaller.RequestWindows

namespace Airbender.UnifiedReduced

/-- Unified caller spans match the complete native worker rows between the same instruction-boundary cuts, with callers
    read from the RV program table. -/
theorem Caller.rv_request_window_soundness : Caller.RVRequestWindowSoundnessClaim := by
  intro p _ hp clockInverse data before addresses accepted inputs lower upper first last pastZero
  exact Caller.Proofs.rv_request_windows hp clockInverse accepted inputs first last pastZero

end Airbender.UnifiedReduced
