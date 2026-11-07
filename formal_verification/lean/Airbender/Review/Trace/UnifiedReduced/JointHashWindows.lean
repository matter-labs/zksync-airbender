import Airbender.Review.Trace.UnifiedReduced.WindowProjection
import Airbender.Review.Trace.Delegation.SharedSpans

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Existing protocol scope for a selected caller-only hash span. G permits
    whole preceding spans in one mode; extended BLAKE/Keccak select the first span. -/
def HashWindowPrefix [Fact p.Prime] (data : RequestTrace p) (span : Delegation.Caller.HashSpan) (lower : Nat) : Prop :=
  match span with
  | .blakeG reduced => (data.workers.prefixRows lower).length % Blake2G.callCount reduced = 0
  | .blakeRound _ => data.workers.prefixRows lower = [] ∧ data.workers.rows.length ≤ 10
  | .keccak => data.workers.prefixRows lower = []

/-- Public shared initialization, original caller bytes, tables and hash ABI.
    Worker boundaries, cut states, ranges and per-row round masks are derived. -/
structure JointHashWindowInputs [Fact p.Prime] (data : RequestTrace p) (before : State)
    (addresses : List (BitVec 32)) (cells : List Cell) (span : Delegation.Caller.HashSpan)
    (lower upper : Nat) : Prop where
  /-- Original public CSR bytes and the initialized machine clock. -/
  publicProgram : RequestInputs data before addresses
  /-- Successful Sail reads construct the joint public seed. -/
  initialization : initialImage before cells = some data.machine.initialMemory
  /-- Each tracked physical address occurs once. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- RAM cells contain aligned four-byte words. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- The unified modeled setup uses this same public memory. -/
  setup : data.machine.rom = Setup.table before
  /-- The unchanged modeled worker tables and Keccak controller. -/
  tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  /-- One hash protocol owns the uninterrupted worker pool. -/
  family : ∀ row ∈ data.workers.rows, row.family = span.family
  /-- The public initial protocol mode/control; entry controls follow from history. -/
  controlStart : (Cell.register span.controlRegister).read before = .ok span.controlStart before
  /-- Prefix scope and the unchanged complete-span call count. -/
  prefixScope : HashWindowPrefix data span lower
  /-- The selected complete span has the existing protocol call count. -/
  calls : (data.workers.windowRows lower upper).length = span.callCount

/-- The complete pinned hash result at the actual joint cut states, with the
    same decoded caller requests and projected native worker boundaries. No
    independent worker permutation or intermediate state is an input. -/
structure JointHashWindowResult [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (span : Delegation.Caller.HashSpan) (lower upper : Nat) : Prop where
  requests : Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper
  count : (Delegation.Caller.windowCallers data.callers lower upper).length = span.callCount
  result : ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
    (atStart atFinish : State),
    earlierEvents.Perm ((data.prefixSteps lower).map transferEvent) ∧
    spanEvents.Perm ((data.windowSteps lower upper).map transferEvent) ∧
    SailHistory cells earlierEvents before atStart ∧ SailHistory cells spanEvents atStart atFinish ∧
    NativeBoundary start atStart cells ∧ NativeBoundary finish atFinish cells ∧
    Delegation.MemoryAccepted (data.windowProjection lower upper start finish) ∧
    Delegation.BoundaryMemoryInputs (data.windowProjection lower upper start finish) atStart (Delegation.Caller.workerCells cells) ∧
    span.Result (data.windowProjection lower upper start finish) atStart atFinish (Delegation.Caller.workerCells cells)

end Airbender.UnifiedReduced.Caller
