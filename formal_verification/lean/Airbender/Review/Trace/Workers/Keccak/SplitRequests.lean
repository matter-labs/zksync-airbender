import Airbender.Review.Trace.Workers.Keccak.SplitNative
import Airbender.Review.Helpers.Delegation.SplitCaller
import Airbender.Review.Helpers.Delegation.Requests
import Airbender.Review.Helpers.Delegation.RequestTrace

namespace Airbender.Keccak.Split.Native
open Airbender.Trace Airbender.Delegation

/-- The actual virtual-register fulfillment from a split worker. Its CSR is
fixed by the compiled worker family and its clock is read from the imported
invocation columns. -/
def Row.fulfillment (cached : Bool) (row : Row p) : Requests.Request p :=
  ⟨row.kind.csr, rawPair row.assignment (row.columns cached).invocation⟩

/-- Machine caller rows and split-worker rows share one full-width virtual CSR
request channel. The program entries are sourced from public Sail bytes by the
separate input boundary, not constructed from the witness here. -/
structure RequestTrace (p : Nat) [Fact p.Prime] where
  machine : PooledTrace p
  workers : MemoryData p
  program : List Split.Caller.ProgramEntry

/-- Select exactly the three blessed split CSR forms from actual ADD/SUB
delegation rows. Other supported workers remain in their own request pools. -/
def RequestTrace.callers [Fact p.Prime] (data : RequestTrace p) :
    List (Airbender.Trace.Row p PooledFamily) :=
  data.machine.rows.filter fun row =>
    row.family == .addSub && decide (Requests.Selected row.assignment) &&
      (Split.Caller.kindOfCSR (Requests.caller row.assignment).csr).isSome

def RequestTrace.calls [Fact p.Prime] (data : RequestTrace p) :
    List (Requests.Request p) :=
  data.callers.map fun row => Requests.caller row.assignment

def RequestTrace.fulfillments [Fact p.Prime] (data : RequestTrace p) :
    List (Requests.Request p) :=
  data.workers.rows.map (Row.fulfillment data.workers.cached)

/-- Native equation/activity facts and exact logical request matching. The
decoder lookup uses all twelve CSR bits; the worker read/write effects and
combined architectural RAM permutation are separate obligations. -/
structure RequestChecks [Fact p.Prime] (data : RequestTrace p) : Prop where
  machineConstraints : ∀ row ∈ data.machine.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints data.machine.rom)
  machineActive : ∀ row ∈ data.machine.rows,
    row.assignment row.columns.execute = 1
  states : (data.machine.initial :: data.machine.rows.map Airbender.Trace.Row.finish).Perm
    (data.machine.terminal :: data.machine.rows.map Airbender.Trace.Row.start)
  decoded : ∀ row ∈ data.callers,
    (Split.Caller.decoderTable data.program).Contains #[]
      (Delegation.Caller.nativeQuery row.assignment)
  workerEquations : EquationsHold data.workers.cached data.workers.setup data.workers.rows
  workerActive : ∀ row ∈ data.workers.rows,
    row.assignment (row.columns data.workers.cached).execute = 1
  requests : Requests.Matching data.calls data.fulfillments

/-- Public split caller bytes and the initial native clock profile. Later
machine clocks are derived from the imported constraints and state matching. -/
structure RequestInputs [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State)
    (addresses : List (BitVec 32)) : Prop where
  image : Split.Caller.programImage before addresses = some data.program
  initialClock : (timeOfPair data.machine.initial.timestamp).Bounded
  initialAligned : (timeOfPair data.machine.initial.timestamp).value % 4 = 0

/-- Consequences of native request matching and the public initial clock:
each issued split caller has one nonzero worker fulfillment at its exact raw
invocation time. Extra zero-clock worker rows remain visible. -/
structure RequestClockBinding [Fact p.Prime] (data : RequestTrace p) : Prop where
  fulfilled : data.calls.Perm
    (data.fulfillments.filter fun request => decide (Requests.Live request))
  clocks : ∀ worker ∈ data.workers.rows,
    (timeOfPair (worker.fulfillment data.workers.cached).time).Bounded
  clockRoom : ∀ worker ∈ data.workers.rows,
    (timeOfPair (worker.fulfillment data.workers.cached).time).lo + 2 < timestampBase
  invocations : (data.calls.map Requests.Request.time).Nodup ∧
    ((data.fulfillments.filter fun request => decide (Requests.Live request)).map
      Requests.Request.time).Nodup

/-- The public split caller's native PC boundary. Worker RAM effects are
separate; this records only source, canonical PC limbs and original Sail
retirement after the native ADD/SUB caller row. -/
structure CallerPCBinding (w : Nat → ZMod p)
    (before : Reference.RiscV.Sail.State)
    (program : List Split.Caller.ProgramEntry) : Prop where
  instruction : ∃ entry ∈ program,
    entry.SourceWith before Split.Caller.decoderFields ∧
      Delegation.Caller.initialPC w = Arithmetic.Word.ofBitVec entry.pc
  bounded : (Delegation.Caller.finalPC w).Bounded
  advances : (Delegation.Caller.finalPC w).toBitVec =
    (Delegation.Caller.initialPC w).toBitVec + 4
  sail : ∀ state : Reference.RiscV.Sail.State,
    Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) state =
      .ok (Delegation.Caller.initialPC w).toBitVec state →
    Reference.Sail.run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) state =
      .ok () { state with regs :=
        (state.regs.insert .nextPC (Delegation.Caller.finalPC w).toBitVec).insert .PC (Delegation.Caller.finalPC w).toBitVec }

end Airbender.Keccak.Split.Native
