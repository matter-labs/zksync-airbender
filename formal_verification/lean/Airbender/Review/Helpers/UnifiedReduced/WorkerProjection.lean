import Airbender.Review.Helpers.UnifiedReduced.MixedMemory
import Airbender.Review.Helpers.Delegation.WorkerProjection

namespace Airbender.UnifiedReduced.Caller

/-- The same native workers with seed/terminal tokens projected from unified
    shared matching. The proof uses an empty ordinary-instruction registry to
    establish that machine rows touch only x0; no caller selector is supplied.
    This projection supports complete worker spans, not arbitrary ISA interleaving. -/
def RequestTrace.workerProjection [Fact p.Prime] (data : RequestTrace p) : Delegation.MemoryData p :=
  data.workers.workerProjection data.machine.initialMemory data.machine.terminalMemory

end Airbender.UnifiedReduced.Caller
