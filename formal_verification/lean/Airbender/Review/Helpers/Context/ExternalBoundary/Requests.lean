import Airbender.Review.Helpers.UnifiedReduced.RequestTrace

namespace Airbender.ExternalBoundary.Requests
open Trace UnifiedReduced.Caller

/-- Occurrence-level accounting over the full CSR and both invocation limbs.
    This strengthens virtual-token matching when zero-clock workers are allowed.
    Current native BabyBear worker constraints exclude active zero clocks;
    `Proofs/ExternalBoundary/NativeRequests.lean` derives this ledger from those
    constraints and initialized caller accounting. The generic contract is
    retained for interfaces that do not select that native constraint profile. -/
def Binding [Fact p.Prime] (data : RequestTrace p) : Prop :=
  data.calls.Perm data.fulfillments

/-- Full worker-to-caller coverage at native slots. Request soundness supplies
    unique fulfillment; occurrence accounting supplies total coverage. -/
def Covered [Fact p.Prime] (data : RequestTrace p) : Prop :=
  ∀ worker ∈ data.workers.rows, ∃ caller ∈ data.callers,
    Delegation.Requests.fulfillment worker = request caller.assignment ∧
    Delegation.Caller.WorkerSlot caller worker

end Airbender.ExternalBoundary.Requests
