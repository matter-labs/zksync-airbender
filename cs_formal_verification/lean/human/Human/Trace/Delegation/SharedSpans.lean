import Human.Helpers.Delegation.WorkerProjection
import Human.Trace.Workers.Blake2G.WorkVector
import Human.Trace.Workers.Blake2Round.Compression
import Human.Trace.Workers.Keccak.Permutation
import Human.Helpers.Delegation.SpanABI

namespace Airbender.Delegation.Caller
open Trace Reference.RiscV.Sail

/-- One complete worker span in the caller-only shared architecture.
    Both public initialization and the existing protocol ABI stay visible. -/
structure SharedSpanInputs [Fact p.Prime] (data : RequestTrace p)
    (before : State) (addresses : List (BitVec 32)) (cells : List Cell)
    (span : HashSpan) : Prop extends SharedMemoryInputs data before addresses cells,
      HashSpan.Protocol data.workers before span

/-- Every shared terminal token is read from the same actual final Sail state,
    including x0 caller tokens and all worker registers/RAM. -/
def SharedTerminalState [Fact p.Prime] (data : RequestTrace p) (after : State)
    (cells : List Cell) : Prop :=
  ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
    cell.addressCode = token.address ∧ cell.read after = .ok token.word.toBitVec after

/-- The already reviewed complete hash reference on actual initial/final RAM.
    `TraceMapping` connects the supplied native worker boundaries to that same
    final state. Caller claims derive those boundaries from shared matching. -/
def HashSpan.Result [Fact p.Prime] (span : HashSpan) (workers : MemoryData p)
    (before after : State) (cells : List Cell) : Prop :=
  match span with
  | .blakeG reduced =>
    ∃ statePointer messagePointer : BitVec 32, ∃ input message output : Vector Arithmetic.Word 16,
      Blake2G.WorkVector.WordMapping before after statePointer messagePointer input message output ∧
      Delegation.TraceMapping workers before after cells ∧
      output.map Arithmetic.Word.value = Blake2G.WorkVector.run reduced input message
  | .blakeRound flags =>
    ∃ statePointer messagePointer : BitVec 32, ∃ input : Blake2Round.Compression.State,
      ∃ message : Vector Arithmetic.Word 16, ∃ output : Blake2Round.Compression.State,
      Blake2Round.Compression.WordMapping before after statePointer messagePointer input output message ∧
      Delegation.TraceMapping workers before after cells ∧
      output = Blake2Round.Compression.run flags input message
  | .keccak =>
    ∃ pointer : BitVec 32, ∃ input output : Vector Nat 25,
      Keccak.Permutation.WordMapping before after pointer input output ∧
      Delegation.TraceMapping workers before after cells ∧
      output = Specs.Keccak256.keccakPermutation input

abbrev SpanResult [Fact p.Prime] (span : HashSpan) (data : RequestTrace p)
    (before after : State) (cells : List Cell) : Prop :=
  span.Result data.workerProjection before after (workerCells cells)

/-- Original decoded requests, the complete existing hash reference, and all
    shared terminal values are connected. Caller PC retirement and unrestricted
    mixed-ISA/span segmentation are outside this architectural-memory claim. -/
structure SharedSpanEffects [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (span : HashSpan) : Prop where
  requests : RequestBinding data before
  /-- Hash output and shared terminal tokens refer to this one actual final state. -/
  result : ∃ after, SharedTerminalState data after cells ∧ SpanResult span data before after cells

end Airbender.Delegation.Caller
