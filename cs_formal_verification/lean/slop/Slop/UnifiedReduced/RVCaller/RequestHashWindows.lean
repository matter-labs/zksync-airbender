import Human.Trace.UnifiedReduced.RVHashSpans
import Slop.Delegation.RequestWindows
import Slop.Blake2G.RVWindows
import Slop.Blake2Round.RVWindows
import Slop.Keccak.RVWindows

/-! RV sibling of `Delegation/RequestHashWindows.lean` (`bind_hash_window`): decoded caller requests and the complete RV
    hash reference (delegate link included) bind the same native window. -/

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Delegation.Caller
variable {Kind : Type} [CircuitLayout Kind]
set_option warningAsError true

theorem rv_bind_hash_window [Fact p.Prime] (hp : 16777216 ≤ p)
    (wordInverse : 64 * (-31457280 : ZMod p) = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {callers : List (Trace.Row p Kind)} {workers : Delegation.MemoryData p} {before : RV.State}
    {cells : List Cell} {span : HashSpan} {lower upper : Nat} (accepted : Delegation.MemoryAccepted workers)
    (inputs : rvRequestWindowInputs span workers before cells lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (binding : RequestWindowBinding callers workers lower upper) :
    RVRequestWindowResult span callers workers before cells lower upper := by
  have family : ∀ worker ∈ workers.windowRows lower upper, worker.family = span.family := by
    intro worker member
    cases span with
    | blakeG reduced => exact inputs.family worker (List.mem_of_mem_filter member)
    | blakeRound flags => exact inputs.family worker (List.mem_of_mem_filter member)
    | keccak => exact inputs.family worker (List.mem_of_mem_filter member)
  have calls : (workers.windowRows lower upper).length = span.callCount := by
    cases span <;> exact inputs.calls
  have callers := Proofs.window_hash_calls binding family calls
  refine ⟨binding, ?_, callers.1, callers.2⟩
  cases span with
  | blakeG reduced => exact Blake2G.Proofs.rv_window_binding (by omega) wordInverse accepted inputs aligned
  | blakeRound flags => exact Blake2Round.Proofs.rv_window_binding (by omega) wordInverse accepted inputs aligned
  | keccak => exact Keccak.Proofs.rv_window_binding hp byteInverse accepted inputs aligned

end Airbender.UnifiedReduced.Caller.Proofs
