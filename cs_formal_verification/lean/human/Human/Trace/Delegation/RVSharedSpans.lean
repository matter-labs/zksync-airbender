module
public import Human.Helpers.Delegation.RVSharedMemory
public import Human.Helpers.Delegation.RVSpanABI
public import Human.Trace.Workers.Blake2G.RVCall
public import Human.Trace.Workers.Blake2Round.RVCall
public import Human.Trace.Workers.Keccak.RVCall

@[expose] public section

namespace Airbender.Delegation.Caller
open Trace

/-- The worker family's RV span result. It is the complete hash reference on actual
    initial/final RV RAM (RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END`), the same
    final state executing every native access (`RVTraceMapping`), and the delegate link: the final state IS the spec's
    run of the span's delegation calls (`RV.calls`) from `before`, up to the spec's PC advance. -/
def HashSpan.RVResult [Fact p.Prime] (span : HashSpan) (workers : MemoryData p)
    (before after : RV.State) (cells : List Cell) : Prop :=
  match span with
  | .blakeG reduced => Blake2G.RVSpanResult reduced workers before after cells
  | .blakeRound flags => Blake2Round.RVSpanResult flags workers before after cells
  | .keccak => Keccak.RVSpanResult workers before after cells

/-- One complete worker span in the caller-only shared RV architecture. -/
structure RVSharedSpanInputs [Fact p.Prime] (data : RVRequestTrace p)
    (before : RV.State) (addresses : List (BitVec 32)) (cells : List Cell)
    (span : HashSpan) : Prop extends RVSharedMemoryInputs data before addresses cells,
      HashSpan.RVProtocol data.workers before span

/-- Every shared terminal token is read (`Cell.readRV`) from the same final
    `RV.State`. -/
def RVSharedTerminalState [Fact p.Prime] (data : RVRequestTrace p) (after : RV.State)
    (cells : List Cell) : Prop :=
  ∀ token ∈ data.machine.terminalMemory, ∃ cell ∈ cells,
    cell.addressCode = token.address ∧ cell.readRV after = some token.word.toBitVec

abbrev RVSpanResult [Fact p.Prime] (span : HashSpan) (data : RVRequestTrace p)
    (before after : RV.State) (cells : List Cell) : Prop :=
  span.RVResult data.workerProjection before after (workerCells cells)

/-- Decoded RV caller requests, the complete hash reference with its delegate link,
    and all shared terminal values, on one actual final `RV.State`. -/
structure RVSharedSpanEffects [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (cells : List Cell) (span : HashSpan) : Prop where
  requests : RVRequestBinding data before
  result : ∃ after, RVSharedTerminalState data after cells ∧ RVSpanResult span data before after cells

end Airbender.Delegation.Caller
