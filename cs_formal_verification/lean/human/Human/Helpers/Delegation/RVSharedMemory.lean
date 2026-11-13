module
public import Human.Helpers.Delegation.WorkerProjection
public import Human.Helpers.Delegation.RVRequestTrace
public import Human.Helpers.Delegation.RequestEffects
public import Human.Helpers.Delegation.SharedMemory

@[expose] public section

/-! The caller-only shared architecture over `RVRequestTrace`: one initialized pool read from an `RV.State` (`initialImageRV`).
    A RAM cell is RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`
    (`RV.State.delegationRAM`); no pointer is required to be at or above `ROM_END`. -/

namespace Airbender.Delegation.Caller
open Trace

/-- Caller x0 transfers and worker register/RAM transfers in one pool. -/
def RVRequestTrace.sharedSteps [Fact p.Prime] (data : RVRequestTrace p) :=
  data.machine.rows.flatMap (fun row => architecturalSteps row.assignment) ++ data.workers.steps

/-- Request checks hold, caller rows are the machine rows, and the shared steps balance initial against terminal
    memory. -/
structure RVSharedMemoryAccepted [Fact p.Prime] (data : RVRequestTrace p) : Prop
    extends RVRequestChecks data where
  callerRows : data.callers = data.machine.rows
  memory : (data.machine.initialMemory ++ data.sharedSteps.map Prod.snd).Perm
    (data.machine.terminalMemory ++ data.sharedSteps.map Prod.fst)

/-- Public RV caller table, starting clock and the single shared seed image read
    from `before` (`initialImageRV`). -/
structure RVSharedMemoryInputs [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (addresses : List (BitVec 32)) (cells : List Cell) : Prop where
  publicProgram : RVRequestInputs data before addresses
  initialization : initialImageRV before cells = some data.machine.initialMemory
  distinct : (cells.map Cell.addressCode).Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned

/-- The shared public RV architecture plus the modeled operation tables and the
    extended BLAKE round-mask ABI. -/
structure RVSharedOperationInputs [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (addresses : List (BitVec 32))
    (cells : List Cell) : Prop extends RVSharedMemoryInputs data before addresses cells where
  tables : data.workers.setup = modeledSetup Keccak.Controller.rows
  rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round

/-- Every shared access and terminal token has bounded words (state-free). -/
structure RVSharedWordBounds [Fact p.Prime] (data : RVRequestTrace p) : Prop where
  accesses : ∀ edge ∈ data.sharedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded
  terminal : ∀ token ∈ data.machine.terminalMemory, token.word.Bounded

/-- The actual workers with non-x0 boundaries from the shared pool. -/
def RVRequestTrace.workerProjection [Fact p.Prime] (data : RVRequestTrace p) : MemoryData p :=
  data.workers.workerProjection data.machine.initialMemory data.machine.terminalMemory

end Airbender.Delegation.Caller
