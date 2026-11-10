module
public import Slop.NonVacuous.UnifiedPrepared
public import Human.Trace.UnifiedReduced.RVCallerTheorems

@[expose] public section

/-! The assumptions of the unified control-preparation caller claims can be met: the trace of
    `Slop/NonVacuous/UnifiedPrepared.lean` (`LUI x10, 0x400` at clock 4, the bigint call at clock 8, `LUI x10, 0x400`
    again at clock 12; cuts 8 and 16, the worker written at clock 11 in between). -/

namespace Airbender.UnifiedReduced.Caller
open NonVacuous.UnifiedPrepared

theorem rv_control_preparation_soundness_satisfiable : RVControlPreparationSoundnessSatisfiableClaim :=
  ⟨data, program, before, [4], [0, 8], cells, 8, 10, .lui 0x400, accepted, inputs, preparation, by decide, rfl,
    callers_ne⟩

theorem rv_control_preparation_window_soundness_satisfiable :
    RVControlPreparationWindowSoundnessSatisfiableClaim :=
  ⟨data, program, before, [4], [0, 8], cells, 8, 16, 10, 10, .lui 0x400, .lui 0x400, accepted, inputs, preparation,
    preparation_again, by decide, by decide, rfl, rfl, by decide, callers_ne, window_ne⟩

end Airbender.UnifiedReduced.Caller
