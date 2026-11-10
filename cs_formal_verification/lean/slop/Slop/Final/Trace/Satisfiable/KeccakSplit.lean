module
public import Slop.NonVacuous.KeccakSplitPool
public import Human.Trace.Workers.KeccakSplit.RVTheorems
public import Human.Trace.WritesRangeChecked

@[expose] public section

/-! The assumptions of the split-Keccak operation and write-range claims can be met: the one-row column-parity pool
    of `Slop/NonVacuous/KeccakSplitPool.lean`. -/

namespace Airbender.Keccak.Split.Native
open NonVacuous.KeccakSplit

theorem rv_operation_execution_satisfiable : RVOperationExecutionSatisfiableClaim :=
  ⟨data, before, cells, accepted, operation_inputs, aligned, native, List.mem_singleton_self _⟩

theorem writes_range_checked_satisfiable : WritesRangeCheckedSatisfiableClaim :=
  ⟨data, accepted, active, native, List.mem_singleton_self _, reads_bounded⟩

end Airbender.Keccak.Split.Native
