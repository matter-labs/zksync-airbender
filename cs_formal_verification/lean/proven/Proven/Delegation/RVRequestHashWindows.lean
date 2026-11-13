module
public import Human.Trace.Delegation.RVRequestHashWindows
public import Proven.Delegation.RVSchedule
public import Proven.Final.Trace.Workers.Blake2G.RVTheorems
public import Proven.Final.Trace.Workers.Blake2Round.RVTheorems
public import Proven.Final.Trace.Workers.Keccak.RVTheorems

@[expose] public section

/-! RV sibling of `bind_hash_window` (`RequestHashWindows.lean`): the request window binding and the RV worker window
    theorems (whose span results carry the delegate link) on the same selected worker rows. -/

namespace Airbender.Delegation.Caller.Proofs
open Trace
variable {Kind : Type} [CircuitLayout Kind]
set_option warningAsError true

theorem rv_bind_hash_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (wordInverse : 64 * (-31457280 : ZMod p) = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {callers : List (Trace.Row p Kind)} {workers : MemoryData p} {before : RV.State} {cells : List Cell}
    {span : HashSpan} {lower upper : Nat} (accepted : MemoryAccepted workers)
    (inputs : span.RVRequestWindowInputs workers before cells lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (binding : RequestWindowBinding callers workers lower upper) :
    span.RVRequestWindowResult callers workers before cells lower upper := by
  have family : ∀ worker ∈ workers.windowRows lower upper, worker.family = span.family := by
    intro worker member
    cases span with
    | blakeG reduced => exact inputs.family worker (List.mem_of_mem_filter member)
    | blakeRound flags => exact inputs.family worker (List.mem_of_mem_filter member)
    | keccak => exact inputs.family worker (List.mem_of_mem_filter member)
  have calls : (workers.windowRows lower upper).length = span.callCount := by
    cases span <;> exact inputs.calls
  have callers := window_hash_calls binding family calls
  refine ⟨binding, ?_, callers.1, callers.2⟩
  cases span with
  | blakeG reduced => exact Blake2G.Native.rv_window_soundness_generic (by omega) wordInverse accepted inputs aligned
  | blakeRound flags => exact Blake2Round.Native.rv_window_soundness_generic (by omega) wordInverse accepted inputs aligned
  | keccak => exact Keccak.Native.rv_window_soundness_generic hp byteInverse accepted inputs aligned

end Airbender.Delegation.Caller.Proofs
