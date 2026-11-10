module
public import Slop.NonVacuous.UnifiedCaller
public import Human.Trace.UnifiedReduced.RVCallerTheorems

@[expose] public section

/-! The assumptions of the unified caller claims with an empty ordinary program (or none) can be met: the caller
    trace of `Slop/NonVacuous/UnifiedCaller.lean` (one bigint caller at clock four, its worker written at clock seven,
    window `(4, 8]`). The claims with an ordinary program are witnessed in `UnifiedPreparedCallers.lean`. -/

namespace Airbender.UnifiedReduced.Caller
open NonVacuous.UnifiedCaller

theorem rv_request_window_soundness_satisfiable : RVRequestWindowSoundnessSatisfiableClaim :=
  ⟨data, before, [0], 4, 8, checks, request_inputs, rfl, rfl, by decide, callers_ne, window_ne⟩

theorem rv_window_projection_soundness_satisfiable : RVWindowProjectionSoundnessSatisfiableClaim :=
  ⟨data, before, [0], [], cells, 4, 8, accepted, inputs, rfl, rfl, by decide, by decide, callers_ne, window_ne⟩

theorem rv_window_schedule_soundness_satisfiable : RVWindowScheduleSoundnessSatisfiableClaim := by
  refine ⟨data, before, [0], 4, 8, checks, request_inputs, rfl, rfl, by decide, by decide, by decide +kernel,
    by decide +kernel, ?_, callers_ne, window_ne⟩
  rw [window_rows]
  rfl

end Airbender.UnifiedReduced.Caller
