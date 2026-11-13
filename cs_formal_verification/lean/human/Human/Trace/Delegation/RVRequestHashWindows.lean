module
public import Human.Helpers.Delegation.RequestWindows
public import Human.Trace.Delegation.RVHashWindows
public import Human.Trace.Delegation.RVSharedSpans

@[expose] public section

namespace Airbender.Delegation.Caller
open Trace
variable {Kind : Type} [CircuitLayout Kind]

/-- The worker families' RV native-window ABI (public controls read by
    `Cell.readRV`, modeled tables, span sizes). -/
def HashSpan.RVRequestWindowInputs [Fact p.Prime] (span : HashSpan) (workers : MemoryData p)
    (before : RV.State) (cells : List Cell) (lower upper : Nat) : Prop :=
  match span with
  | .blakeG reduced => Blake2G.RVWindowInputs workers before cells reduced lower upper
  | .blakeRound flags => Blake2Round.RVWindowInputs workers before cells flags lower upper
  | .keccak => Keccak.RVWindowInputs workers before cells lower upper

/-- Actual decoded caller requests and the complete hash reference
    (`HashSpan.RVResult` at history-derived RV cut states, with the delegate link: the window's final state IS the spec's
    run of the span's delegation calls) use the same selected native worker rows. RAM cells include READ-WRITE ACCESS
    TO THE SHADOW RAM BELOW `ROM_END`. -/
structure HashSpan.RVRequestWindowResult [Fact p.Prime] (span : HashSpan)
    (callers : List (Trace.Row p Kind)) (workers : MemoryData p)
    (before : RV.State) (cells : List Cell) (lower upper : Nat) : Prop extends
      RequestWindowBinding callers workers lower upper where
  reference : RVWindowResult span.RVResult workers before cells lower upper
  count : (windowCallers callers lower upper).length = span.callCount
  family : ∀ caller ∈ windowCallers callers lower upper,
    (Requests.caller caller.assignment).csr = Requests.csr span.family

end Airbender.Delegation.Caller
