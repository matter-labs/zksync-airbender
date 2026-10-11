import Airbender.Review.UnifiedReduced.Delegation
import Airbender.Review.Delegation.Schedule

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Read the unified artifact's caller selector. Original public decoding below
    checks its meaning; this filter supplies no instruction or worker result. -/
def Selected (w : Nat → ZMod p) : Prop := w importedConstraintsDecoderColumns.flags[7] = 1
instance (w : Nat → ZMod p) : Decidable (Selected w) := inferInstanceAs
  (Decidable (w importedConstraintsDecoderColumns.flags[7] = 1))

/-- Actual unified machine rows and delegation workers sharing one request pool.
    Architectural GPR/RAM matching is a separate next connection. -/
structure RequestTrace (p : Nat) [Fact p.Prime] where
  /-- Imported unified PC/clock rows and their public boundaries. -/
  machine : UnifiedTrace p
  /-- Actual imported worker assignments and modeled setup. -/
  workers : Delegation.MemoryData p
  /-- Caller entries obtained from public bytes by the original Sail decoder. -/
  program : List ProgramEntry

def RequestTrace.callers [Fact p.Prime] (data : RequestTrace p) :=
  data.machine.rows.filter fun row => decide (Selected row.assignment)
def RequestTrace.calls [Fact p.Prime] (data : RequestTrace p) :=
  data.callers.map fun row => request row.assignment
def RequestTrace.fulfillments [Fact p.Prime] (data : RequestTrace p) :=
  data.workers.rows.map Delegation.Requests.fulfillment

/-- Native equations, participation and exact logical request matching.
    No invocation bounds, desired worker, result or schedule is assumed. -/
structure RequestChecks [Fact p.Prime] (data : RequestTrace p) : Prop where
  /-- Imported richer machine equations and timestamp queries. -/
  constraints : ∀ row ∈ data.machine.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.machine.rom)
  /-- Each included machine row participates. -/
  active : ∀ row ∈ data.machine.rows, row.assignment row.columns.execute = 1
  /-- Exact native PC/clock matching, including the public endpoints. -/
  states : (data.machine.initial :: data.machine.rows.map Trace.Row.finish).Perm
    (data.machine.terminal :: data.machine.rows.map Trace.Row.start)
  /-- Selected callers use the original public full-width CSR table. -/
  decoded : ∀ row ∈ data.callers, (decoderTable data.program).Contains #[] (decoderQuery row.assignment)
  /-- Actual worker equations and native range/timestamp queries. -/
  workerConstraints : ∀ row ∈ data.workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.workers.setup)
  /-- Included workers participate; inactive padding is outside this pool. -/
  workerActive : ∀ row ∈ data.workers.rows, row.assignment row.columns.execute = 1
  /-- The virtual CSR permutation is separate from initialized architectural memory. -/
  requests : Delegation.Requests.Matching data.calls data.fulfillments

/-- Public bytes and the initial native clock. State matching and equations
    derive every later clock, invocation bound and caller/worker correspondence. -/
structure RequestInputs [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32)) : Prop where
  /-- Successful public byte reads and original Sail decoding construct the table. -/
  image : programImage before addresses = some data.program
  /-- The public initial clock has two canonical nineteen-bit limbs. -/
  initialClock : (timeOfPair data.machine.initial.timestamp).Bounded
  /-- The machine starts on its four-tick instruction stride. -/
  initialAligned : (timeOfPair data.machine.initial.timestamp).value % 4 = 0

/-- Unified caller/worker identity and timing proved from that same native pool.
    This binds requests, not architectural reads or whole-call ISA retirement.
    Zero-clock surplus workers remain exposed by `unissued`. -/
structure RequestBinding [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) : Prop where
  /-- Original decoding binds full-width requests, x0 destination and PC advancement. -/
  callers : ∀ row ∈ data.callers, Binding row.assignment before data.program
  /-- Exact request multiplicity covers all nonzero worker invocations. -/
  fulfilled : data.calls.Perm (data.fulfillments.filter fun call => decide (Delegation.Requests.Live call))
  /-- Each actual caller has exactly one actual worker in its native cycle.
      The family follows from the full CSR binding above. -/
  workers : ∀ row ∈ data.callers, ∃! worker,
    worker ∈ data.workers.rows ∧ Delegation.Requests.fulfillment worker = request row.assignment ∧
      Delegation.Caller.WorkerSlot row worker
  /-- Initialized machine clocks and request matching derive every worker's
      invocation bounds and room for its native write offset. -/
  clocks : ∀ worker ∈ data.workers.rows,
    (decodeTimestamp worker.assignment worker.columns.invocation).Bounded ∧
      (decodeTimestamp worker.assignment worker.columns.invocation).lo + 2 < timestampBase
  /-- Issued clocks and live fulfillment clocks are unique; no ordering is assumed. -/
  invocations : (data.calls.map Delegation.Requests.Request.time).Nodup ∧
    ((data.fulfillments.filter fun call => decide (Delegation.Requests.Live call)).map
      Delegation.Requests.Request.time).Nodup
  /-- Every unissued worker has zero invocation, and conversely. This retains
      the flagged surplus-worker gap rather than excluding it with a premise. -/
  unissued : ∀ worker ∈ data.workers.rows,
    (¬ ∃ row ∈ data.callers, Delegation.Requests.fulfillment worker = request row.assignment) ↔
      (Delegation.Requests.fulfillment worker).time = (0, 0)
  /-- No machine instruction starts strictly inside an issued caller's cycle. -/
  separated : ∀ caller ∈ data.callers, ∀ row ∈ data.machine.rows,
    ¬ (Delegation.Caller.startClock caller < Delegation.Caller.startClock row ∧
      Delegation.Caller.startClock row < Delegation.Caller.finishClock caller)

end Airbender.UnifiedReduced.Caller
