import Human.Trace.UnifiedReduced.PreparedHashWindows

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- One prepared extended-BLAKE controller region; earlier workers remain outside it. -/
structure RoundRegion where
  flags : Fin 8
  lower : Nat
  upper : Nat

end Airbender.UnifiedReduced.Caller
