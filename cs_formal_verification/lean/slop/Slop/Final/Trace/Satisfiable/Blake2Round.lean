module
public import Slop.NonVacuous.Blake2RoundPool
public import Slop.NonVacuous.Blake2RoundSpan.Span
public import Human.Trace.Workers.Blake2Round.RVTheorems

@[expose] public section

/-! The assumptions of the extended-control Blake2s round claims can be met: the operation claim by the one-row round
    pool of `Slop/NonVacuous/Blake2RoundPool.lean`, the complete-span compression, boundary and window claims by the
    ten-round plain-mode span of `Slop/NonVacuous/Blake2RoundSpan/Span.lean` (the window: the whole span after an
    empty prefix). -/

namespace Airbender.Blake2Round.Native
open NonVacuous.Blake2Round

theorem rv_operation_execution_satisfiable : RVOperationExecutionSatisfiableClaim :=
  ⟨data, before, cells, control, accepted, operation_inputs, aligned, native, List.mem_singleton_self _, rfl⟩

theorem rv_compression_soundness_satisfiable : RVCompressionSoundnessSatisfiableClaim :=
  ⟨NonVacuous.Blake2RoundSpan.data, NonVacuous.Blake2RoundSpan.before, NonVacuous.Blake2RoundSpan.cells, 0,
    NonVacuous.Blake2RoundSpan.accepted, NonVacuous.Blake2RoundSpan.call_inputs, NonVacuous.Blake2RoundSpan.aligned⟩

theorem rv_compression_boundary_soundness_satisfiable : RVCompressionBoundarySoundnessSatisfiableClaim :=
  ⟨NonVacuous.Blake2RoundSpan.data, NonVacuous.Blake2RoundSpan.before, NonVacuous.Blake2RoundSpan.cells, 0,
    NonVacuous.Blake2RoundSpan.accepted, NonVacuous.Blake2RoundSpan.native_call_inputs,
    NonVacuous.Blake2RoundSpan.aligned⟩

theorem rv_window_soundness_satisfiable : RVWindowSoundnessSatisfiableClaim :=
  ⟨NonVacuous.Blake2RoundSpan.data, NonVacuous.Blake2RoundSpan.before, NonVacuous.Blake2RoundSpan.cells, 0, 0, 1000,
    NonVacuous.Blake2RoundSpan.accepted, NonVacuous.Blake2RoundSpan.window_inputs, NonVacuous.Blake2RoundSpan.aligned⟩

end Airbender.Blake2Round.Native
