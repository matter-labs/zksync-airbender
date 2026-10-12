import Airbender.Review.UnifiedReduced.WorkerProjection
import Airbender.Review.Delegation.SharedSpans

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Public inputs for a complete hash span in the unified caller pool.
    An empty ordinary-instruction registry establishes caller-only rows.
    The existing mode and span-size ABI stays explicit; no operand ranges,
    per-row round masks, intermediate states or worker boundaries are supplied. -/
structure SharedSpanInputs [Fact p.Prime] (data : RequestTrace p)
    (before : State) (addresses : List (BitVec 32)) (cells : List Cell)
    (span : Delegation.Caller.HashSpan) : Prop extends
      RequestInputs data before addresses,
      Delegation.Caller.HashSpan.Protocol data.workers before span where
  /-- Successful reads of the public initial state construct the shared seed. -/
  initialization : initialImage before cells = some data.machine.initialMemory
  /-- Each physical address is initialized once. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- RAM cells represent aligned four-byte words. -/
  aligned : ∀ cell ∈ cells, cell.Aligned

/-- All terminal tokens, including architectural x0 and worker registers/RAM,
    are read from this same actual final Sail state. -/
def SharedTerminalState [Fact p.Prime] (data : RequestTrace p) (after : State)
    (cells : List Cell) : Prop :=
  ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
    cell.addressCode = token.address ∧ cell.read after = .ok token.word.toBitVec after

/-- Original decoded requests and the existing complete hash reference reach
    one actual shared terminal state. Worker boundaries come from global memory
    matching. Caller PC retirement and arbitrary mixed-ISA/span segmentation
    remain outside this memory-effect claim. -/
structure SharedSpanEffects [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (span : Delegation.Caller.HashSpan) : Prop where
  /-- Public decoding and native matching identify each issued worker. -/
  requests : RequestBinding data before
  /-- The pinned hash reference and every terminal cell use the same state. -/
  result : ∃ after, SharedTerminalState data after cells ∧
    span.Result data.workerProjection before after (Delegation.Caller.workerCells cells)

end Airbender.UnifiedReduced.Caller
