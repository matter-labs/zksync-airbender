import Human.Helpers.Delegation.RVRequestTrace
import Human.Helpers.Delegation.RequestEffects

namespace Airbender.Delegation.Caller
open Trace

/-- RV sibling of `RequestOperationInputs`: public RV worker seeds (`RVRequestMemoryInputs`; RAM cells include the
    shadow RAM below `ROM_END`), the modeled operation tables and the extended BLAKE round-mask ABI. -/
structure RVRequestOperationInputs [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (addresses : List (BitVec 32))
    (cells : List Cell) : Prop where
  publicState : RVRequestMemoryInputs data before addresses cells
  tables : data.workers.setup = modeledSetup Keccak.Controller.rows
  rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round

end Airbender.Delegation.Caller
