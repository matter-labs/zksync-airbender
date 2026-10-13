import Airbender.Review.Helpers.UnifiedReduced.Windows

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Joint machine/worker memory transport between aligned instruction cuts. Both
    boundary states, reads and tokens come from one initialized history. This
    exposes control preparation effects; instruction retirement remains separate. -/
structure MixedWindowExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (lower upper : Nat) : Prop where
  /-- Exact selected caller/worker requests, counts and unique native slots. -/
  requests : Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper
  /-- Complete selected rows, exact architectural matching and actual cut states. -/
  execution : ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
    (atStart atFinish : State),
    earlierEvents.Perm ((data.prefixSteps lower).map transferEvent) ∧
    spanEvents.Perm ((data.windowSteps lower upper).map transferEvent) ∧
    SailHistory cells earlierEvents before atStart ∧ SailHistory cells spanEvents atStart atFinish ∧
    (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps lower).map Prod.fst) ∧
    (start ++ (data.windowSteps lower upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps lower upper).map Prod.fst) ∧
    NativeBoundary start atStart cells ∧ NativeBoundary finish atFinish cells

end Airbender.UnifiedReduced.Caller
