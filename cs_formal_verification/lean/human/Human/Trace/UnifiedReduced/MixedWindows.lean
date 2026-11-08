import Human.Helpers.Delegation.RequestWindows
import Human.Helpers.UnifiedReduced.MixedMemory

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Public ordered, aligned window intervals; gaps and empty intervals are allowed. -/
def WindowsOrdered (cut : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (lower, upper) :: rest => cut ≤ lower ∧ lower ≤ upper ∧ lower % 4 = 0 ∧ upper % 4 = 0 ∧
      WindowsOrdered upper rest

end Airbender.UnifiedReduced.Caller
