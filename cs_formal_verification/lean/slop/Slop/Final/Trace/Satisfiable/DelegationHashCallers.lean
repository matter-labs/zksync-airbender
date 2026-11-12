module
public import Slop.NonVacuous.HashCallers.Pooled
public import Human.Trace.Delegation.RVCallerTheorems

@[expose] public section

/-! The assumptions of the delegation complete-span caller claims can be met: the six-family caller trace of
    `Slop/NonVacuous/HashCallers/Pooled.lean` (56 ADD/SUB G callers at clocks `4 + 4 k`, the reduced G span invoked
    at `5 + 4 k`, window `(4, 228]`). -/

namespace Airbender.Delegation.Caller
open NonVacuous.HashCallers NonVacuous.HashCallers.Pooled
open NonVacuous.FamilyCallers (callerPCs)

theorem rv_shared_span_soundness_satisfiable : RVSharedSpanSoundnessSatisfiableClaim :=
  ⟨data, before, callerPCs 0 56, keys, .blakeG true, shared_accepted, shared_span_inputs, callers_ne⟩

theorem rv_request_hash_window_soundness_satisfiable : RVRequestHashWindowSoundnessSatisfiableClaim :=
  ⟨data, before, callerPCs 0 56, NonVacuous.Blake2GSpan.cells, .blakeG true, 4, 228, accepted, request_inputs,
    window_inputs, NonVacuous.Blake2GSpan.aligned, rfl, rfl, by decide, callers_ne, window_ne⟩

end Airbender.Delegation.Caller
