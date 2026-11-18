module
public import Proven.Bigint.RVNativeExecution
public import Human.Trace.Workers.Bigint.RVTheorems

@[expose] public section

namespace Airbender.Bigint.Native

/-- RV sibling of `operation_execution` (statement of `RVOperationExecutionClaim`): the seven selected operations on
    actual RV port reads/writes (RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`), and every
    bigint row is one spec bigint call (`RVCalls`). -/
theorem rv_operation_execution {data : Delegation.MemoryData babyBearModulus}
    {before : RV.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.RVMemoryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (table : data.setup.bigint = setupTable) :
    Delegation.RVMemoryExecution data before cells ∧
      (∀ row ∈ data.rows, row.family = .bigint → ArithmeticEffects row.assignment) ∧
      RVCalls data before cells :=
  Proofs.rv_operation_execution accepted inputs aligned table

end Airbender.Bigint.Native
