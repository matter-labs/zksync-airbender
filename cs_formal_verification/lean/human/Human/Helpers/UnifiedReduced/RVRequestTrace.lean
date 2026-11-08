module
public import Human.Helpers.UnifiedReduced.RequestTrace
public import Human.Helpers.UnifiedReduced.RVProgram
public import Human.Helpers.Delegation.RVDecoder
public import Human.Helpers.Context.RVRowContext

@[expose] public section

/-! The unified caller request trace: the caller program is an RV program table (ROM bytes decoded by `RV.decode` to `.delegate k`, `csrrw x0, csr, x0`),
    and the public state is an `RV.State`. Native selectors, ports and request tokens are the unified machine's own.
    The caller table is the shared delegation caller table (`Delegation.Caller.rvProgramImage`, `rvDecoderTable`). -/

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic

/-- Actual unified machine rows and delegation workers sharing one request pool; the
    caller entries come from the RV program table. -/
structure RVRequestTrace (p : Nat) [Fact p.Prime] where
  machine : UnifiedTrace p
  workers : Delegation.MemoryData p
  program : List Delegation.Caller.RVProgramEntry

def RVRequestTrace.callers [Fact p.Prime] (data : RVRequestTrace p) :=
  data.machine.rows.filter fun row => decide (Selected row.assignment)
def RVRequestTrace.calls [Fact p.Prime] (data : RVRequestTrace p) :=
  data.callers.map fun row => request row.assignment
def RVRequestTrace.fulfillments [Fact p.Prime] (data : RVRequestTrace p) :=
  data.workers.rows.map Delegation.Requests.fulfillment

/-- Native equations, participation and exact logical request matching; selected
    callers use the RV caller table. -/
structure RVRequestChecks [Fact p.Prime] (data : RVRequestTrace p) : Prop where
  constraints : ∀ row ∈ data.machine.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.machine.rom)
  active : ∀ row ∈ data.machine.rows, row.assignment row.columns.execute = 1
  states : (data.machine.initial :: data.machine.rows.map Trace.Row.finish).Perm
    (data.machine.terminal :: data.machine.rows.map Trace.Row.start)
  decoded : ∀ row ∈ data.callers, (Delegation.Caller.rvDecoderTable data.program).Contains #[] (decoderQuery row.assignment)
  workerConstraints : ∀ row ∈ data.workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.workers.setup)
  workerActive : ∀ row ∈ data.workers.rows, row.assignment row.columns.execute = 1
  requests : Delegation.Requests.Matching data.calls data.fulfillments

/-- The RV ROM image and `RV.decode` construct the caller table; the initial native
    clock. -/
structure RVRequestInputs [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (addresses : List (BitVec 32)) : Prop where
  image : Delegation.Caller.rvProgramImage before addresses = some data.program
  initialClock : (timeOfPair data.machine.initial.timestamp).Bounded
  initialAligned : (timeOfPair data.machine.initial.timestamp).value % 4 = 0

/-- What the RV caller table and the unified equations prove about a caller. The entry is read
    from the ROM image and decodes to `.delegate k` of its family; `RV.step` at any state with that ROM image and the
    row's starting PC is `RV.exec` of that delegation call. x0 reads 0 and the native zero write to x0 leaves the state
    unchanged. -/
structure RVBinding (w : Nat → ZMod p) (before : RV.State) (program : List Delegation.Caller.RVProgramEntry) : Prop where
  instruction : ∃ entry ∈ program, Delegation.Caller.RVSource before entry ∧
    RV.decode entry.bits = some (.delegate entry.data.family.rvKind) ∧
    (request w).csr = Delegation.Requests.csr entry.data.family ∧
    ∀ state : RV.State, state.rom = before.rom → state.pc = (initialPC w).toBitVec →
      RV.step state = RV.exec state (.delegate entry.data.family.rvKind)
  selected : w importedConstraintsTraceColumns.execute = 1 ∧
    w importedConstraintsDecoderColumns.flags[7] = 1
  virtual : readToken w virtualPort = (request w).empty ∧
    writeToken importedConstraintsTraceColumns w virtualPort = (request w).issued
  registers : (sourceToken w).address = (Cell.register 0).addressCode ∧
    (destinationToken w).address = (Cell.register 0).addressCode ∧
    (destinationToken w).word = ⟨0, 0⟩
  pc : (initialPC w).Bounded ∧ (finalPC w).Bounded ∧
    (finalPC w).toBitVec = (initialPC w).toBitVec + 4
  registerEffects : ∀ state : RV.State, (Cell.register 0).readRV state = some 0 ∧
    (Cell.register 0).applyRV (destinationToken w).word.toBitVec state = some state

/-- Unified caller/worker identity and timing from the same native pool. -/
structure RVRequestBinding [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State) : Prop where
  callers : ∀ row ∈ data.callers, RVBinding row.assignment before data.program
  fulfilled : data.calls.Perm (data.fulfillments.filter fun call => decide (Delegation.Requests.Live call))
  workers : ∀ row ∈ data.callers, ∃! worker,
    worker ∈ data.workers.rows ∧ Delegation.Requests.fulfillment worker = request row.assignment ∧
      Delegation.Caller.WorkerSlot row worker
  clocks : ∀ worker ∈ data.workers.rows,
    (decodeTimestamp worker.assignment worker.columns.invocation).Bounded ∧
      (decodeTimestamp worker.assignment worker.columns.invocation).lo + 2 < timestampBase
  invocations : (data.calls.map Delegation.Requests.Request.time).Nodup ∧
    ((data.fulfillments.filter fun call => decide (Delegation.Requests.Live call)).map
      Delegation.Requests.Request.time).Nodup
  unissued : ∀ worker ∈ data.workers.rows,
    (¬ ∃ row ∈ data.callers, Delegation.Requests.fulfillment worker = request row.assignment) ↔
      (Delegation.Requests.fulfillment worker).time = (0, 0)
  separated : ∀ caller ∈ data.callers, ∀ row ∈ data.machine.rows,
    ¬ (Delegation.Caller.startClock caller < Delegation.Caller.startClock row ∧
      Delegation.Caller.startClock row < Delegation.Caller.finishClock caller)

end Airbender.UnifiedReduced.Caller
