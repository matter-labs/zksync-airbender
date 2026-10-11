import Airbender.Review.Delegation.SharedMemory
import Airbender.Review.Delegation.RequestEffects

namespace Airbender.Delegation.Caller
open Trace

/-- The shared public architecture plus the existing modeled operation tables.
    Extended BLAKE round-mask exclusivity remains an explicit ABI condition;
    worker participation and clock room come from request acceptance. -/
structure SharedOperationInputs [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (addresses : List (BitVec 32))
    (cells : List Cell) : Prop extends SharedMemoryInputs data before addresses cells where
  /-- The pinned modeled tables, including the concrete Keccak controller. -/
  tables : data.workers.setup = modeledSetup Keccak.Controller.rows
  /-- One admitted extended BLAKE round per worker; span ABI is still separate. -/
  rounds : ∀ row ∈ data.workers.rows, row.family = .blakeRound →
    ∃ round, Blake2Round.Memory.RoundMask row.assignment round

/-- Canonical words at every caller/worker access and shared terminal cell.
    Bounds propagate through the single initialized architecture, including
    transfers between worker invocations; they are proved, not supplied. -/
structure SharedWordBounds [Fact p.Prime] (data : RequestTrace p) : Prop where
  /-- Every imported architectural read and write is an RV32 word. -/
  accesses : ∀ edge ∈ data.sharedSteps, edge.1.word.Bounded ∧ edge.2.word.Bounded
  /-- Every declared shared terminal value is an RV32 word. -/
  terminal : ∀ token ∈ data.machine.terminalMemory, token.word.Bounded

/-- Requests, native Sail transfers and all four operation references use the
    same architectural pool. Shared history supplies source values, pointers,
    operands and word bounds. Whole-call span ABI and mixed ISA composition
    remain open; this admits caller machine rows only. -/
structure SharedOperationEffects [Fact p.Prime] (data : RequestTrace p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  /-- Caller/worker transfers execute from one public seed image to its terminal. -/
  memory : SharedMemoryEffects data before cells
  /-- No per-worker operand, pointer or result-range premise remains. -/
  words : SharedWordBounds data
  /-- Existing bigint/Clean hash references on those same native port values. -/
  operations : ∀ row ∈ data.workers.rows, WorkerEffect row

end Airbender.Delegation.Caller
