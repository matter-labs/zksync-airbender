import Airbender.Review.UnifiedReduced.WindowProjection

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Clock matching and a public four-tick duration derive a caller-only region
    inside a mixed trace. Ordinary rows may occur before and after the cuts. -/
structure CallerWindowSchedule [Fact p.Prime] (data : RequestTrace p) (lower upper : Nat) : Prop where
  /-- Exact instruction count from accepted state matching and clock advancement. -/
  machineCount : (data.windowMachineRows lower upper).length = (upper - lower) / 4
  /-- Every selected machine row is an actual caller, in its native list order. -/
  rows : Delegation.Caller.windowCallers data.callers lower upper = data.windowMachineRows lower upper
  /-- Each selected caller has one selected worker; surplus workers stay outside. -/
  workerCount : (data.windowMachineRows lower upper).length = (data.workers.windowRows lower upper).length

/-- A derived caller region projects to worker matching at the actual mixed
    cut states. Earlier ordinary effects remain in the joint prefix history. -/
structure MixedProjectedWindowExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (lower upper : Nat) : Prop where
  schedule : CallerWindowSchedule data lower upper
  requests : Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper
  execution : ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
    (atStart atFinish : State),
    earlierEvents.Perm ((data.prefixSteps lower).map transferEvent) ∧
    spanEvents.Perm ((data.windowSteps lower upper).map transferEvent) ∧
    SailHistory cells earlierEvents before atStart ∧ SailHistory cells spanEvents atStart atFinish ∧
    (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps lower).map Prod.fst) ∧
    (start ++ (data.windowSteps lower upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps lower upper).map Prod.fst) ∧
    NativeBoundary start atStart cells ∧ NativeBoundary finish atFinish cells ∧
    Delegation.MemoryAccepted (data.windowProjection lower upper start finish) ∧
    Delegation.BoundaryMemoryInputs (data.windowProjection lower upper start finish) atStart (Delegation.Caller.workerCells cells) ∧
    NativeBoundary (data.windowProjection lower upper start finish).terminal atFinish (Delegation.Caller.workerCells cells) ∧
    Delegation.TraceMapping (data.windowProjection lower upper start finish) atStart atFinish (Delegation.Caller.workerCells cells)

end Airbender.UnifiedReduced.Caller
