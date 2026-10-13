import Airbender.Review.UnifiedReduced.MixedWindows
import Airbender.Review.UnifiedReduced.WorkerProjection
import Airbender.Review.Delegation.BoundaryMemory

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

/-- Derived prefix/window worker matching and Sail transport at the same joint
    cut states. The empty ordinary registry establishes caller-only rows.
    Full mixed instruction interleaving and ISA retirement remain separate. -/
structure ProjectedWindowExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (lower upper : Nat) : Prop where
  requests : Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper
  execution : ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
    (atStart atFinish : State),
    earlierEvents.Perm ((data.prefixSteps lower).map transferEvent) ∧
    spanEvents.Perm ((data.windowSteps lower upper).map transferEvent) ∧
    SailHistory cells earlierEvents before atStart ∧ SailHistory cells spanEvents atStart atFinish ∧
    NativeBoundary start atStart cells ∧ NativeBoundary finish atFinish cells ∧
    Delegation.MemoryAccepted (data.prefixProjection lower start) ∧
    Delegation.TraceMapping (data.prefixProjection lower start) before atStart (Delegation.Caller.workerCells cells) ∧
    Delegation.MemoryAccepted (data.windowProjection lower upper start finish) ∧
    Delegation.BoundaryMemoryInputs (data.windowProjection lower upper start finish) atStart (Delegation.Caller.workerCells cells) ∧
    NativeBoundary (data.windowProjection lower upper start finish).terminal atFinish (Delegation.Caller.workerCells cells) ∧
    Delegation.TraceMapping (data.windowProjection lower upper start finish) atStart atFinish (Delegation.Caller.workerCells cells)

end Airbender.UnifiedReduced.Caller
