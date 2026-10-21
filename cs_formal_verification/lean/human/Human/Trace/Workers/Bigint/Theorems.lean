import Human.Circuits.Bigint.Execution
import Human.Helpers.Core.BabyBearPrime
import Human.Trace.Delegation.Execution

-- The statements proven in slop/Slop/Final/Trace/Workers/Bigint/Theorems.lean (checked by verify.sh).

namespace Airbender.Bigint.Native

/-- All seven selected bigint operations act on the values realized by actual
    Sail port reads/writes, with exact terminal cells and unchanged frame.
    Other delegation families may share the history. Only public initialization,
    alignment, logical matching and the modeled bigint table are supplied.
    Caller ABI/request binding remains separate; the flagged no-opcode case
    is not silently ruled out by this theorem. -/
def OperationExecutionClaim : Prop :=
  ∀ {data : Delegation.MemoryData babyBearModulus} {before : Reference.RiscV.Sail.State} {cells : List Trace.Cell} (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.MemoryInputs data before cells) (aligned : ∀ cell ∈ cells, cell.Aligned) (table : data.setup.bigint = setupTable),
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .bigint → ArithmeticEffects row.assignment

end Airbender.Bigint.Native
