module
public import Human.Helpers.Delegation.RVDecoder
public import Human.Helpers.Delegation.RVMemory
public import Human.Helpers.Context.Registries.Pooled

@[expose] public section

/-! Caller/worker request records: the public caller table is the RV table
    (`rvProgramImage`, `RV.decode`), the public starting point is an `RV.State`, seed cells are read by `Cell.readRV`.
    A RAM cell is RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`
    (`RV.State.delegationRAM`); no pointer is required to be at or above `ROM_END`. -/

namespace Airbender.Delegation.Caller
open Trace

/-- The six-family machine path, the actual worker pool and the public RV caller table. -/
structure RVRequestTrace (p : Nat) [Fact p.Prime] where
  /-- The six-family machine path, including its ADD/SUB caller rows. -/
  machine : PooledTrace p
  /-- Actual worker assignments, setup and native memory boundary tokens. -/
  workers : MemoryData p
  /-- Entries produced from public ROM bytes by `RV.decode`. -/
  program : List RVProgramEntry

/-- The selected ADD/SUB caller rows (as `RequestTrace.callers`). -/
def RVRequestTrace.callers [Fact p.Prime] (data : RVRequestTrace p) : List (Trace.Row p PooledFamily) :=
  data.machine.rows.filter (fun row => row.family == .addSub && decide (Requests.Selected row.assignment))

def RVRequestTrace.calls [Fact p.Prime] (data : RVRequestTrace p) : List (Requests.Request p) :=
  data.callers.map (fun row => Requests.caller row.assignment)

def RVRequestTrace.fulfillments [Fact p.Prime] (data : RVRequestTrace p) : List (Requests.Request p) :=
  data.workers.rows.map Requests.fulfillment

/-- The same native equations, participation flags and exact logical matching; caller
    decoder membership is in the RV caller table. -/
structure RVRequestChecks [Fact p.Prime] (data : RVRequestTrace p) : Prop where
  constraints : ∀ row ∈ data.machine.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints data.machine.rom)
  active : ∀ row ∈ data.machine.rows, row.assignment row.columns.execute = 1
  states : (data.machine.initial :: data.machine.rows.map Trace.Row.finish).Perm
    (data.machine.terminal :: data.machine.rows.map Trace.Row.start)
  /-- Each selected caller's actual decoder query belongs to the public RV caller table. -/
  decoded : ∀ row ∈ data.callers,
    (rvDecoderTable data.program).Contains #[] (nativeQuery row.assignment)
  workerConstraints : ∀ row ∈ data.workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints data.workers.setup)
  workerActive : ∀ row ∈ data.workers.rows, row.assignment row.columns.execute = 1
  requests : Requests.Matching data.calls data.fulfillments

/-- The request checks plus the worker-only native memory matching. -/
structure RVRequestAccepted [Fact p.Prime] (data : RVRequestTrace p) : Prop extends RVRequestChecks data where
  workerMemory : (data.workers.initial ++ data.workers.steps.map Prod.snd).Perm
    (data.workers.terminal ++ data.workers.steps.map Prod.fst)

def RVRequestAccepted.workers [Fact p.Prime] {data : RVRequestTrace p}
    (accepted : RVRequestAccepted data) : MemoryAccepted data.workers :=
  ⟨accepted.workerConstraints, accepted.workerMemory⟩

/-- The public RV caller table and initial-clock conditions. -/
structure RVRequestInputs [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (addresses : List (BitVec 32)) : Prop where
  /-- Public ROM reads and `RV.decode` construct the caller table. -/
  image : rvProgramImage before addresses = some data.program
  initialClock : (timeOfPair data.machine.initial.timestamp).Bounded
  initialAligned : (timeOfPair data.machine.initial.timestamp).value % 4 = 0

/-- Every public caller (an RV delegation call `.delegate k`, `RVBinding`) is fulfilled
    by a worker of the decoded family at the exact issued invocation; native clock room is proved for the pool. -/
structure RVRequestBinding [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State) : Prop where
  callers : ∀ row ∈ data.callers,
    RVBinding row.assignment before data.program ∧ RVPCBinding row.assignment before data.program
  fulfilled : data.calls.Perm (data.fulfillments.filter (fun request => decide (Requests.Live request)))
  /-- Actual native worker rows fulfill every caller, with the family of the caller's decoded delegation. -/
  workers : ∀ row ∈ data.callers, ∃ worker ∈ data.workers.rows,
    Requests.fulfillment worker = Requests.caller row.assignment ∧
    ∃ entry ∈ data.program, RVSource before entry ∧ worker.family = entry.data.family
  clocks : ∀ row ∈ data.workers.rows, (decodeTimestamp row.assignment row.columns.invocation).Bounded
  clockRoom : ∀ row ∈ data.workers.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase
  invocations : (data.calls.map Requests.Request.time).Nodup ∧
    ((data.fulfillments.filter (fun request => decide (Requests.Live request))).map Requests.Request.time).Nodup

/-- The worker pool's seed tokens are RV reads of public cells (`initialImageRV`;
    RAM cells include the shadow RAM below `ROM_END`). -/
structure RVRequestMemoryInputs [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (addresses : List (BitVec 32)) (cells : List Cell) : Prop where
  publicProgram : RVRequestInputs data before addresses
  initialization : initialImageRV before cells = some data.workers.initial
  distinct : (cells.map Cell.addressCode).Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned

end Airbender.Delegation.Caller
