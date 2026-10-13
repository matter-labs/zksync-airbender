import Airbender.Review.Helpers.UnifiedReduced.Windows
import Airbender.Review.Helpers.UnifiedReduced.WorkerProjection
import Airbender.Review.Helpers.Delegation.BoundaryMemory

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Worker boundaries projected from the actual joint instruction cuts.
    Caller x0 refreshes are removed; worker-only input boundaries are unused. -/
def RequestTrace.windowProjection [Fact p.Prime] (data : RequestTrace p) (lower upper : Nat)
    (start finish : List (MemoryToken p)) : Delegation.MemoryData p :=
  ⟨data.workers.setup, data.workers.windowRows lower upper,
    start.filter fun token => token.address != (Cell.register 0).addressCode,
    finish.filter fun token => token.address != (Cell.register 0).addressCode⟩

/-- Earlier workers retain the shared public seed and the actual first cut. -/
def RequestTrace.prefixProjection [Fact p.Prime] (data : RequestTrace p) (lower : Nat)
    (start : List (MemoryToken p)) : Delegation.MemoryData p :=
  ⟨data.workers.setup, data.workers.prefixRows lower, data.workerProjection.initial,
    start.filter fun token => token.address != (Cell.register 0).addressCode⟩

end Airbender.UnifiedReduced.Caller
