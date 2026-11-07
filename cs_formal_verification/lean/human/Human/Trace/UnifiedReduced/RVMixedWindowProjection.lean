import Human.Trace.UnifiedReduced.RVWindowProjection

/-! RV siblings of the Sail-stated unified caller window contracts (same file name without `RV`): states are
    `RV.State`s, cells are read by `Cell.readRV` and executed by `RVHistory`, programs are RV program tables. A RAM cell
    is RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`). -/

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- A derived caller region projects to worker matching at the actual mixed
    cut states. Earlier ordinary effects remain in the joint prefix history. -/
structure RVMixedProjectedWindowExecution [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (cells : List Cell) (lower upper : Nat) : Prop where
  schedule : RVCallerWindowSchedule data lower upper
  requests : Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper
  execution : ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
    (atStart atFinish : RV.State),
    earlierEvents.Perm ((data.prefixSteps lower).map transferEvent) ∧
    spanEvents.Perm ((data.windowSteps lower upper).map transferEvent) ∧
    RVHistory cells earlierEvents before atStart ∧ RVHistory cells spanEvents atStart atFinish ∧
    (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps lower).map Prod.fst) ∧
    (start ++ (data.windowSteps lower upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps lower upper).map Prod.fst) ∧
    RVNativeBoundary start atStart cells ∧ RVNativeBoundary finish atFinish cells ∧
    Delegation.MemoryAccepted (data.windowProjection lower upper start finish) ∧
    Delegation.RVBoundaryMemoryInputs (data.windowProjection lower upper start finish) atStart (Delegation.Caller.workerCells cells) ∧
    RVNativeBoundary (data.windowProjection lower upper start finish).terminal atFinish (Delegation.Caller.workerCells cells) ∧
    Delegation.RVTraceMapping (data.windowProjection lower upper start finish) atStart atFinish (Delegation.Caller.workerCells cells)

end Airbender.UnifiedReduced.Caller
