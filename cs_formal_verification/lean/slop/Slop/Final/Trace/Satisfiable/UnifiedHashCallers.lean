module
public import Slop.NonVacuous.HashCallers.Unified
public import Human.Trace.UnifiedReduced.RVCallerTheorems

@[expose] public section

/-! The assumptions of the unified complete-span caller claims can be met: the caller-only trace of
    `Slop/NonVacuous/HashCallers/Unified.lean` (56 G callers at clocks `4 + 4 k`, the reduced G span invoked at
    `5 + 4 k`, window `(4, 228]`). -/

namespace Airbender.UnifiedReduced.Caller
open NonVacuous.HashCallers NonVacuous.HashCallers.Unified

theorem rv_shared_span_soundness_satisfiable : RVSharedSpanSoundnessSatisfiableClaim :=
  ⟨data, before, callerPCs 0 56, keys, .blakeG true, accepted, shared_span_inputs, callers_ne⟩

theorem rv_request_hash_window_soundness_satisfiable : RVRequestHashWindowSoundnessSatisfiableClaim :=
  ⟨data, before, callerPCs 0 56, NonVacuous.Blake2GSpan.cells, .blakeG true, 4, 228, checks,
    accepted_from start, request_inputs, window_inputs, NonVacuous.Blake2GSpan.aligned, rfl, rfl, by decide,
    callers_ne, window_ne⟩

theorem rv_joint_hash_window_soundness_satisfiable : RVJointHashWindowSoundnessSatisfiableClaim :=
  ⟨data, before, callerPCs 0 56, keys, .blakeG true, 4, 228, accepted, joint_inputs, rfl, rfl, by decide, by decide,
    callers_ne, window_ne⟩

end Airbender.UnifiedReduced.Caller
