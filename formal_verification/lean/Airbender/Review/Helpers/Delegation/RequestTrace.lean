import Airbender.Review.Helpers.Delegation.Decoder
import Airbender.Review.Helpers.Delegation.WorkerContext
import Airbender.Review.Helpers.Context.Registries.Pooled

namespace Airbender.Delegation.Caller
open Trace

/-- The actual machine rows and worker pool share one request channel.
    Machine PC/clock tokens and worker invocation columns stay native.
    This claim binds requests; architectural memory composition is separate. -/
structure RequestTrace (p : Nat) [Fact p.Prime] where
  /-- The six-family machine path, including its ADD/SUB caller rows. -/
  machine : PooledTrace p
  /-- Actual worker assignments, setup and native memory boundary tokens. -/
  workers : MemoryData p
  /-- Entries produced from public bytes by the original Sail decoder. -/
  program : List ProgramEntry

/-- Read the imported selector; this filter does not assume its correctness.
    Decoder membership below ties each selected caller to its public instruction. -/
def RequestTrace.callers [Fact p.Prime] (data : RequestTrace p) : List (Trace.Row p PooledFamily) :=
  data.machine.rows.filter (fun row => row.family == .addSub && decide (Requests.Selected row.assignment))

def RequestTrace.calls [Fact p.Prime] (data : RequestTrace p) : List (Requests.Request p) :=
  data.callers.map (fun row => Requests.caller row.assignment)

def RequestTrace.fulfillments [Fact p.Prime] (data : RequestTrace p) : List (Requests.Request p) :=
  data.workers.rows.map Requests.fulfillment

/-- Check native equations, participation flags and exact logical matching.
    No desired invocation, worker result or per-row clock bound is supplied. -/
structure RequestChecks [Fact p.Prime] (data : RequestTrace p) : Prop where
  /-- Imported machine equations and range queries, for every participating row. -/
  constraints : ∀ row ∈ data.machine.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints data.machine.rom)
  /-- Participating machine rows have their imported execute flag set. -/
  active : ∀ row ∈ data.machine.rows, row.assignment row.columns.execute = 1
  /-- The machine's exact PC/timestamp permutation, including its boundaries. -/
  states : (data.machine.initial :: data.machine.rows.map Trace.Row.finish).Perm
    (data.machine.terminal :: data.machine.rows.map Trace.Row.start)
  /-- Each selected caller's actual decoder query belongs to the public table. -/
  decoded : ∀ row ∈ data.callers,
    (decoderTable data.program).Contains #[] (nativeQuery row.assignment)
  /-- Every worker satisfies its imported equations and lookup queries. -/
  workerConstraints : ∀ row ∈ data.workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints data.workers.setup)
  /-- Participating worker rows are active; inactive padding is outside this pool. -/
  workerActive : ∀ row ∈ data.workers.rows, row.assignment row.columns.execute = 1
  /-- The virtual CSR permutation, kept separate from architectural GPR/RAM tokens. -/
  requests : Requests.Matching data.calls data.fulfillments

/-- The earlier worker-only memory claim. Its request checks are shared with
    the combined caller/worker claim; this extra permutation covers workers alone. -/
structure RequestAccepted [Fact p.Prime] (data : RequestTrace p) : Prop extends RequestChecks data where
  /-- Exact worker-only native memory matching, retained for existing regressions. -/
  workerMemory : (data.workers.initial ++ data.workers.steps.map Prod.snd).Perm
    (data.workers.terminal ++ data.workers.steps.map Prod.fst)

def RequestAccepted.workers [Fact p.Prime] {data : RequestTrace p}
    (accepted : RequestAccepted data) : MemoryAccepted data.workers :=
  ⟨accepted.workerConstraints, accepted.workerMemory⟩

/-- Only public image and initial-clock conditions are needed for request binding.
    Shared state matching derives every later clock; no worker timestamp-room
    condition or assumed caller/worker correspondence is added. -/
structure RequestInputs [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32)) : Prop where
  /-- Public byte reads and original Sail decoding construct the caller table. -/
  image : programImage before addresses = some data.program
  /-- Both limbs of the public initial machine clock are nineteen-bit values. -/
  initialClock : (timeOfPair data.machine.initial.timestamp).Bounded
  /-- The public initial machine clock follows the four-tick instruction stride. -/
  initialAligned : (timeOfPair data.machine.initial.timestamp).value % 4 = 0

/-- Every public caller is fulfilled by a worker of the decoded family at the
    exact issued invocation. Native clock room is proved for the worker pool.
    Extra zero-clock workers remain possible and are explicitly retained. -/
structure RequestBinding [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) : Prop where
  /-- Public decoding, native virtual tokens, destination zero and Sail PC effects. -/
  callers : ∀ row ∈ data.callers,
    Binding row.assignment before data.program ∧ PCBinding row.assignment before data.program
  /-- Caller requests match exactly the nonzero worker requests, with multiplicity. -/
  fulfilled : data.calls.Perm (data.fulfillments.filter (fun request => decide (Requests.Live request)))
  /-- Actual native worker rows, not newly constructed witnesses, fulfill every caller. -/
  workers : ∀ row ∈ data.callers, ∃ worker ∈ data.workers.rows,
    Requests.fulfillment worker = Requests.caller row.assignment ∧
    ∃ entry ∈ data.program, entry.SourceWith before decoderFields ∧ worker.family = entry.data.family
  /-- Every worker's two native invocation limbs are canonical nineteen-bit values. -/
  clocks : ∀ row ∈ data.workers.rows, (decodeTimestamp row.assignment row.columns.invocation).Bounded
  /-- The native write offset two never crosses the low-limb boundary. -/
  clockRoom : ∀ row ∈ data.workers.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase

  /-- Every issued invocation clock occurs once, and every live fulfillment
      occurs once at its matching clock. Unissued zero-clock workers stay visible. -/
  invocations : (data.calls.map Requests.Request.time).Nodup ∧
    ((data.fulfillments.filter (fun request => decide (Requests.Live request))).map Requests.Request.time).Nodup

/-- Bind the worker pool's seed tokens to actual public Sail cells. Request
    matching supplies timestamp room internally; these fields give only public
    initialization and the physical tracked-cell domain. -/
structure RequestMemoryInputs [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32))
    (cells : List Cell) : Prop where
  /-- Public caller bytes and initial machine-clock conditions. -/
  publicProgram : RequestInputs data before addresses
  /-- Successful reads construct the worker pool's initial native tokens. -/
  initialization : initialImage before cells = some data.workers.initial
  /-- One public seed per tracked register/RAM address. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- RAM cells use aligned four-byte words; GPR cells are always aligned. -/
  aligned : ∀ cell ∈ cells, cell.Aligned

end Airbender.Delegation.Caller
