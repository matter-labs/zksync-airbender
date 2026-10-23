import Airbender.Proofs.Bigint.MemorySoundness
import Airbender.Proofs.Bigint.NativeExecution

namespace Airbender.Bigint.Native

/-- All seven selected bigint operations act on the values realized by actual
    Sail port reads/writes, with exact terminal cells and unchanged frame.
    Other delegation families may share the history. Only public initialization,
    alignment, logical matching and the modeled bigint table are supplied.
    Caller ABI/request binding remains separate; the flagged no-opcode case
    is not silently ruled out by this theorem. -/
theorem operation_execution {data : Delegation.MemoryData babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.MemoryInputs data before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (table : data.setup.bigint = setupTable) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .bigint → ArithmeticEffects row.assignment :=
  Proofs.native_operation_execution accepted inputs aligned table

end Airbender.Bigint.Native
