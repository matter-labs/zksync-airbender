import Airbender.Review.Helpers.Context.ExternalBoundary.Requests
import Airbender.Proofs.Delegation.NativeInvocation
import Airbender.Proofs.BabyBear

namespace Airbender.ExternalBoundary.Requests.Proofs
open Trace UnifiedReduced.Caller
set_option warningAsError true

/-- Current native worker constraints exclude the self-cancelling zero-clock
    token. Existing initialized caller accounting therefore covers every
    worker occurrence, without an external ledger premise. -/
theorem native_binding {data : RequestTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} (accepted : RequestChecks data)
    (native : RequestBinding data before) : Binding data := by
  have live : data.fulfillments.filter (fun request => decide (Delegation.Requests.Live request)) =
      data.fulfillments := by
    apply List.filter_eq_self.mpr
    intro request member
    obtain ⟨row, present, rfl⟩ := List.mem_map.mp member
    exact decide_eq_true (Delegation.Proofs.active_invocation_live
      (accepted.workerConstraints row present) (accepted.workerActive row present))
  change data.calls.Perm data.fulfillments
  simpa only [live] using native.fulfilled

end Airbender.ExternalBoundary.Requests.Proofs
