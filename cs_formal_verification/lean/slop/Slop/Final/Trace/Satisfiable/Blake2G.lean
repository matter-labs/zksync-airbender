module
public import Slop.NonVacuous.Blake2GPool
public import Human.Trace.Workers.Blake2G.RVTheorems

@[expose] public section

/-! The assumptions of the Blake2s G operation claim can be met: the one-row G pool of
    `Slop/NonVacuous/Blake2GPool.lean`. -/

namespace Airbender.Blake2G.Native
open NonVacuous.Blake2G

theorem rv_operation_execution_satisfiable : RVOperationExecutionSatisfiableClaim :=
  ⟨data, before, cells, control, accepted, operation_inputs, aligned, native, List.mem_singleton_self _, rfl⟩

end Airbender.Blake2G.Native
