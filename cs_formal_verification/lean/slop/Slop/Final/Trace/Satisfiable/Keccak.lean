module
public import Slop.NonVacuous.KeccakPool
public import Slop.NonVacuous.KeccakSpan.Span
public import Human.Trace.Workers.Keccak.RVTheorems

@[expose] public section

/-! The assumptions of the Keccak special5 claims can be met: the operation claim by the one-row Keccak pool of
    `Slop/NonVacuous/KeccakPool.lean`, the complete-span permutation, boundary and window claims by the 649-call
    span of `Slop/NonVacuous/KeccakSpan/Span.lean` (the window: the whole span after an empty prefix). -/

namespace Airbender.Keccak.Native
open NonVacuous.Keccak

theorem rv_operation_execution_satisfiable : RVOperationExecutionSatisfiableClaim :=
  ⟨data, before, cells, accepted, operation_inputs, aligned, native, List.mem_singleton_self _, rfl⟩

theorem rv_permutation_soundness_satisfiable : RVPermutationSoundnessSatisfiableClaim :=
  ⟨NonVacuous.KeccakSpan.data, NonVacuous.KeccakSpan.before, NonVacuous.KeccakSpan.cells,
    NonVacuous.KeccakSpan.accepted, NonVacuous.KeccakSpan.call_inputs, rfl, NonVacuous.KeccakSpan.aligned⟩

theorem rv_permutation_boundary_soundness_satisfiable : RVPermutationBoundarySoundnessSatisfiableClaim :=
  ⟨NonVacuous.KeccakSpan.data, NonVacuous.KeccakSpan.before, NonVacuous.KeccakSpan.cells,
    NonVacuous.KeccakSpan.accepted, NonVacuous.KeccakSpan.native_call_inputs, rfl, NonVacuous.KeccakSpan.aligned⟩

theorem rv_window_soundness_satisfiable : RVWindowSoundnessSatisfiableClaim :=
  ⟨NonVacuous.KeccakSpan.data, NonVacuous.KeccakSpan.before, NonVacuous.KeccakSpan.cells, 0, 4000,
    NonVacuous.KeccakSpan.accepted, NonVacuous.KeccakSpan.window_inputs, NonVacuous.KeccakSpan.aligned⟩

end Airbender.Keccak.Native
