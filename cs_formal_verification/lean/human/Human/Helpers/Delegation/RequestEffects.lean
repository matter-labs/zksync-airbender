import Human.Helpers.Delegation.RequestTrace
import Human.Circuits.Bigint.Execution
import Human.Circuits.Blake2G.Execution
import Human.Circuits.Blake2Round.Execution
import Human.Circuits.Keccak.Execution

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

/-- Public initialized worker state and existing modeled tables. The extended
    BLAKE round mask remains an explicit ABI boundary; request matching alone
    does not establish its exclusivity. Worker clock room and Keccak participation
    are derived from the accepted machine/request channel. -/
structure RequestOperationInputs [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32))
    (cells : List Cell) : Prop where
  /-- Actual public program, worker seed cells and aligned address domain. -/
  publicState : RequestMemoryInputs data before addresses cells
  /-- The four modeled operation tables, with Keccak's concrete controller. -/
  tables : data.workers.setup = modeledSetup Keccak.Controller.rows
  /-- The admitted extended BLAKE ABI selects one round per worker. -/
  rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round

end Airbender.Delegation.Caller
