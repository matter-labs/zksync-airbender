module
public import Slop.NonVacuous.KeccakPool
public import Human.Trace.Workers.Keccak.RVTheorems

@[expose] public section

/-! The assumptions of the Keccak special5 operation claim can be met: the one-row Keccak pool of
    `Slop/NonVacuous/KeccakPool.lean`. -/

namespace Airbender.Keccak.Native
open NonVacuous.Keccak

theorem rv_operation_execution_satisfiable : RVOperationExecutionSatisfiableClaim :=
  ⟨data, before, cells, accepted, operation_inputs, aligned, native, List.mem_singleton_self _, rfl⟩

end Airbender.Keccak.Native
