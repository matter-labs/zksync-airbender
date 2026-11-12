module
public import Slop.NonVacuous.KeccakSplitPool
public import Slop.NonVacuous.KeccakSplitSpan.Span
public import Human.Trace.Workers.KeccakSplit.RVTheorems
public import Human.Trace.WritesRangeChecked

@[expose] public section

/-! The assumptions of the split-Keccak claims can be met: the operation and write-range claims by the one-row
    column-parity pool of `Slop/NonVacuous/KeccakSplitPool.lean`, the permutation claim by the complete 361-call
    request of `Slop/NonVacuous/KeccakSplitSpan/Span.lean`. -/

namespace Airbender.Keccak.Split.Native
open NonVacuous.KeccakSplit

theorem rv_operation_execution_satisfiable : RVOperationExecutionSatisfiableClaim :=
  ⟨data, before, cells, accepted, operation_inputs, aligned, native, List.mem_singleton_self _⟩

theorem writes_range_checked_satisfiable : WritesRangeCheckedSatisfiableClaim :=
  ⟨data, accepted, active, native, List.mem_singleton_self _, reads_bounded⟩

theorem rv_permutation_soundness_satisfiable : RVPermutationSoundnessSatisfiableClaim :=
  ⟨NonVacuous.KeccakSplitSpan.data, NonVacuous.KeccakSplitSpan.before, NonVacuous.KeccakSplitSpan.cells,
    NonVacuous.KeccakSplitSpan.accepted, NonVacuous.KeccakSplitSpan.call_inputs, NonVacuous.KeccakSplitSpan.aligned⟩

end Airbender.Keccak.Split.Native
