import Airbender.Review.Helpers.UnifiedReduced.RequestTrace

namespace Airbender.ExternalBoundary.Requests
open Trace UnifiedReduced.Caller

/-- Temporary strengthened accounting for the open AIH-339 / F03 finding.
    Native request matching does not establish this contract; adding it leaves
    the zero-clock acceptance defect open.
    External occurrence-level delegation accounting over the full CSR and both
    raw invocation limbs. Every actual worker occurrence is in this ledger,
    independently of whether its native issued/empty token happens to coincide.
    This strengthens the existing cancelling virtual-token permutation. It is
    not derived from that permutation, and does not assume positive clocks. -/
def Binding [Fact p.Prime] (data : RequestTrace p) : Prop :=
  data.calls.Perm data.fulfillments

/-- Full worker-to-caller coverage at native slots. Original request soundness
    supplies unique fulfillment; the external ledger supplies total coverage. -/
def Covered [Fact p.Prime] (data : RequestTrace p) : Prop :=
  ∀ worker ∈ data.workers.rows, ∃ caller ∈ data.callers,
    Delegation.Requests.fulfillment worker = request caller.assignment ∧
    Delegation.Caller.WorkerSlot caller worker

end Airbender.ExternalBoundary.Requests
