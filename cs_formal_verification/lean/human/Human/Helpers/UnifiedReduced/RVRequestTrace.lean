import Human.Helpers.UnifiedReduced.RequestTrace
import Human.Helpers.UnifiedReduced.RVProgram
import Human.Helpers.Context.RVRowContext

/-! RV siblings of the unified caller request trace (`RequestTrace.lean`, `Circuits/UnifiedReduced/Delegation.lean`):
    the caller program is an RV program table (ROM bytes decoded by `RV.decode` to `.delegate k`, `csrrw x0, csr, x0`),
    and the public state is an `RV.State`. No `Configured`. Native selectors, ports and request tokens are unchanged.
    (Reconciliation note: `rvCallerFields`, `rvCallerQuery` and `rvCallerTable` are the RV siblings of
    `Delegation.Caller.decoderFields`/`query`/`decoderTable`.) -/

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic

/-- The RV delegation kind called by a worker family. -/
def familyKind : Delegation.Family → RV.DelegationKind
  | .bigint => .bigint
  | .blakeG => .blakeG
  | .blakeRound => .blakeRound
  | .keccak => .keccak

/-- RV sibling of `Delegation.Caller.decoderFields`: the four pinned delegation CSRs (`RV.decode` gives `.delegate k`;
    both architectural operands are x0). The split Keccak kinds have no unified caller. The full CSR stays in the
    query, not in a five-bit register field. -/
def rvCallerFields : RV.Instr → Option (DecoderData Delegation.Family)
  | .delegate .bigint => some ⟨.bigint, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  | .delegate .blakeG => some ⟨.blakeG, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  | .delegate .blakeRound => some ⟨.blakeRound, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  | .delegate .keccak => some ⟨.keccak, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩
  | _ => none

/-- One public caller entry: its PC, ROM bytes and native metadata of `RV.decode` of those bytes. -/
abbrev RVCallerEntry := Trace.RVProgramEntry Delegation.Family

/-- Caller entries read from the ROM image (`RV.read` of `rom`) and decoded by `RV.decode`. -/
noncomputable abbrev rvCallerImage := Trace.rvProgramImageWith rvCallerFields

/-- RV sibling of `Delegation.Caller.query`: the ADD/SUB-placement caller query; its rs2 field is the full CSR. -/
def rvCallerQuery {p : Nat} (entry : RVCallerEntry) : Vector (ZMod p) 9 :=
  let pc := Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, 0, Delegation.Requests.csr entry.data.family, 0, 0, 0, 0, 128]

/-- RV sibling of `Delegation.Caller.decoderTable`: the logical caller table of public RV entries. -/
def rvCallerTable {p : Nat} [Fact p.Prime] (program : List RVCallerEntry) :
    Table (ZMod p) (fields 9) := .fromStatic {
  name := "Airbender.DelegationCaller"
  length := program.length
  row i := rvCallerQuery (program.get i)
  index values := program.toArray.findIdx (fun entry => rvCallerQuery entry == values)
  Spec values := ∃ entry ∈ program, values = rvCallerQuery entry
  contains_iff := by
    intro values
    constructor
    · rintro ⟨i, equal⟩
      exact ⟨program.get i, List.get_mem _ _, equal⟩
    · rintro ⟨entry, member, equal⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
      exact ⟨i, equal⟩ }

/-- RV sibling of `RequestTrace`: actual unified machine rows and delegation workers sharing one request pool; the
    caller entries come from the RV program table. -/
structure RVRequestTrace (p : Nat) [Fact p.Prime] where
  machine : UnifiedTrace p
  workers : Delegation.MemoryData p
  program : List RVCallerEntry

def RVRequestTrace.callers [Fact p.Prime] (data : RVRequestTrace p) :=
  data.machine.rows.filter fun row => decide (Selected row.assignment)
def RVRequestTrace.calls [Fact p.Prime] (data : RVRequestTrace p) :=
  data.callers.map fun row => request row.assignment
def RVRequestTrace.fulfillments [Fact p.Prime] (data : RVRequestTrace p) :=
  data.workers.rows.map Delegation.Requests.fulfillment

/-- RV sibling of `RequestChecks`: native equations, participation and exact logical request matching; selected
    callers use the RV caller table. -/
structure RVRequestChecks [Fact p.Prime] (data : RVRequestTrace p) : Prop where
  constraints : ∀ row ∈ data.machine.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.machine.rom)
  active : ∀ row ∈ data.machine.rows, row.assignment row.columns.execute = 1
  states : (data.machine.initial :: data.machine.rows.map Trace.Row.finish).Perm
    (data.machine.terminal :: data.machine.rows.map Trace.Row.start)
  decoded : ∀ row ∈ data.callers, (rvCallerTable data.program).Contains #[] (decoderQuery row.assignment)
  workerConstraints : ∀ row ∈ data.workers.rows,
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.workers.setup)
  workerActive : ∀ row ∈ data.workers.rows, row.assignment row.columns.execute = 1
  requests : Delegation.Requests.Matching data.calls data.fulfillments

/-- RV sibling of `RequestInputs`: the RV ROM image and `RV.decode` construct the caller table; the initial native
    clock. No `Configured`. -/
structure RVRequestInputs [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (addresses : List (BitVec 32)) : Prop where
  image : rvCallerImage before addresses = some data.program
  initialClock : (timeOfPair data.machine.initial.timestamp).Bounded
  initialAligned : (timeOfPair data.machine.initial.timestamp).value % 4 = 0

/-- RV sibling of `Binding`: what the RV caller table and the unified equations prove about a caller. The entry is read
    from the ROM image and decodes to `.delegate k` of its family; `RV.step` at any state with that ROM image and the
    row's starting PC is `RV.exec` of that delegation call. x0 reads 0 and the native zero write to x0 leaves the state
    unchanged. -/
structure RVBinding (w : Nat → ZMod p) (before : RV.State) (program : List RVCallerEntry) : Prop where
  instruction : ∃ entry ∈ program, rvProgramEntryWith rvCallerFields before entry.pc = some entry ∧
    RV.decode entry.bits = some (.delegate (familyKind entry.data.family)) ∧
    (request w).csr = Delegation.Requests.csr entry.data.family ∧
    ∀ state : RV.State, state.rom = before.rom → state.pc = (initialPC w).toBitVec →
      RV.step state = RV.exec state (.delegate (familyKind entry.data.family))
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

/-- RV sibling of `RequestBinding`: unified caller/worker identity and timing from the same native pool. -/
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
