module
public import Slop.NonVacuous.Blake2RoundPool
public import Human.Trace.Workers.Blake2Round.RVTheorems

@[expose] public section

/-! The assumptions of the extended-control Blake2s round operation claim can be met: the one-row round pool of
    `Slop/NonVacuous/Blake2RoundPool.lean`. -/

namespace Airbender.Blake2Round.Native
open NonVacuous.Blake2Round

theorem rv_operation_execution_satisfiable : RVOperationExecutionSatisfiableClaim :=
  ⟨data, before, cells, control, accepted, operation_inputs, aligned, native, List.mem_singleton_self _, rfl⟩

end Airbender.Blake2Round.Native
