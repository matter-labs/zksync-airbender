import Human.Trace.Delegation.RequestHashWindows
import Human.Trace.Delegation.RVHashWindows
import Human.Trace.Workers.Blake2G.RVCall
import Human.Trace.Workers.Blake2Round.RVCall
import Human.Trace.Workers.Keccak.RVCall

/-! RV siblings of the hash-span contracts used by the unified caller claims (`HashSpan.Protocol`, `HashSpan.Result`,
    `HashSpan.RequestWindowInputs`, `HashSpan.RequestWindowResult`): the public state is an `RV.State`, and the span
    result is the worker family's RV span result (`Blake2G/Blake2Round/Keccak.RVSpanResult`), which includes the
    delegate link: the span's final state IS the spec's run of its `.delegate` calls (`RV.calls`), up to the spec's PC
    advance. RAM cells include READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`).
    (Reconciliation note: these are UR-local names for RV twins of `Delegation.Caller.HashSpan.*`.) -/

namespace Airbender.UnifiedReduced.Caller
open Trace Delegation.Caller

/-- RV sibling of `HashSpan.Protocol`: public mode/control read from an `RV.State` and the homogeneous complete-span
    ABI. -/
structure RVHashSpanProtocol [Fact p.Prime] (workers : Delegation.MemoryData p) (before : RV.State)
    (span : HashSpan) : Prop where
  tables : workers.setup = Delegation.modeledSetup Keccak.Controller.rows
  family : ∀ row ∈ workers.rows, row.family = span.family
  controlStart : (Cell.register span.controlRegister).readRV before = some span.controlStart
  calls : workers.rows.length = span.callCount

/-- RV sibling of `HashSpan.Result`: the family's complete hash reference on actual initial/final RV states, with
    `RVTraceMapping` and the delegate link. -/
def rvSpanResult [Fact p.Prime] (span : HashSpan) (workers : Delegation.MemoryData p)
    (before after : RV.State) (cells : List Cell) : Prop :=
  match span with
  | .blakeG reduced => Blake2G.RVSpanResult reduced workers before after cells
  | .blakeRound flags => Blake2Round.RVSpanResult flags workers before after cells
  | .keccak => Keccak.RVSpanResult workers before after cells

/-- RV sibling of `HashSpan.RequestWindowInputs`: the family's RV native-window ABI. -/
def rvRequestWindowInputs [Fact p.Prime] (span : HashSpan) (workers : Delegation.MemoryData p)
    (before : RV.State) (cells : List Cell) (lower upper : Nat) : Prop :=
  match span with
  | .blakeG reduced => Blake2G.RVWindowInputs workers before cells reduced lower upper
  | .blakeRound flags => Blake2Round.RVWindowInputs workers before cells flags lower upper
  | .keccak => Keccak.RVWindowInputs workers before cells lower upper

/-- RV sibling of `HashSpan.RequestWindowResult`: decoded caller requests and the complete RV hash reference use the
    same selected native worker rows. -/
structure RVRequestWindowResult [Fact p.Prime] {Kind : Type} [CircuitLayout Kind] (span : HashSpan)
    (callers : List (Trace.Row p Kind)) (workers : Delegation.MemoryData p)
    (before : RV.State) (cells : List Cell) (lower upper : Nat) : Prop extends
      RequestWindowBinding callers workers lower upper where
  reference : RVWindowResult (rvSpanResult span) workers before cells lower upper
  count : (windowCallers callers lower upper).length = span.callCount
  family : ∀ caller ∈ windowCallers callers lower upper,
    (Delegation.Requests.caller caller.assignment).csr = Delegation.Requests.csr span.family

end Airbender.UnifiedReduced.Caller
