module
public import Human.Circuits.Bigint.Execution
public import Human.Circuits.Blake2G.Execution
public import Human.Circuits.Blake2Round.Execution
public import Human.Circuits.Keccak.Execution

@[expose] public section

namespace Airbender.Delegation.Caller
open Trace

/-- Existing operation references, applied to this worker's actual native port
    observations. The family comes from the imported row and request channel;
    no expected operation result is supplied here. -/
def WorkerEffect (row : Delegation.Row p) : Prop :=
  match row.family with
  | .bigint => Bigint.Native.ArithmeticEffects row.assignment
  | .blakeG => Blake2G.spec (Blake2G.Native.input row.assignment) (Blake2G.Native.output row.assignment)
  | .blakeRound => ∃ round, Blake2Round.Memory.RoundMask row.assignment round ∧
      Blake2Round.Row.spec (Blake2Round.Native.input round row.assignment) (Blake2Round.Native.output row.assignment)
  | .keccak => Keccak.Native.RowEffects row.assignment

end Airbender.Delegation.Caller
