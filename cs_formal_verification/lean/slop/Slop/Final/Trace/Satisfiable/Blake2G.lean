module
public import Slop.NonVacuous.Blake2GPool
public import Slop.NonVacuous.Blake2GSpan.Span
public import Human.Trace.Workers.Blake2G.RVTheorems

@[expose] public section

/-! The assumptions of the Blake2s G claims can be met: the operation claim by the one-row G pool of
    `Slop/NonVacuous/Blake2GPool.lean`, the complete-span work-vector, boundary and window claims by the 56-row
    reduced span of `Slop/NonVacuous/Blake2GSpan/Span.lean` (the window: the whole span after an empty prefix). -/

namespace Airbender.Blake2G.Native
open NonVacuous.Blake2G

theorem rv_operation_execution_satisfiable : RVOperationExecutionSatisfiableClaim :=
  ⟨data, before, cells, control, accepted, operation_inputs, aligned, native, List.mem_singleton_self _, rfl⟩

theorem rv_workvector_soundness_satisfiable : RVWorkvectorSoundnessSatisfiableClaim :=
  ⟨NonVacuous.Blake2GSpan.data, NonVacuous.Blake2GSpan.before, NonVacuous.Blake2GSpan.cells, true,
    NonVacuous.Blake2GSpan.accepted, NonVacuous.Blake2GSpan.call_inputs, NonVacuous.Blake2GSpan.aligned⟩

theorem rv_workvector_boundary_soundness_satisfiable : RVWorkvectorBoundarySoundnessSatisfiableClaim :=
  ⟨NonVacuous.Blake2GSpan.data, NonVacuous.Blake2GSpan.before, NonVacuous.Blake2GSpan.cells, true,
    NonVacuous.Blake2GSpan.accepted, NonVacuous.Blake2GSpan.native_call_inputs, NonVacuous.Blake2GSpan.aligned⟩

theorem rv_window_soundness_satisfiable : RVWindowSoundnessSatisfiableClaim :=
  ⟨NonVacuous.Blake2GSpan.data, NonVacuous.Blake2GSpan.before, NonVacuous.Blake2GSpan.cells, true, 0, 1000,
    NonVacuous.Blake2GSpan.accepted, NonVacuous.Blake2GSpan.window_inputs, NonVacuous.Blake2GSpan.aligned⟩

end Airbender.Blake2G.Native
