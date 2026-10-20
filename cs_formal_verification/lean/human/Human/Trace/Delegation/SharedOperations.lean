import Human.Trace.Delegation.SharedMemory
import Human.Helpers.Delegation.SharedOperations

namespace Airbender.Delegation.Caller
open Trace

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
