import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Trace.Delegation.RequestHashWindows
import Airbender.Proofs.Delegation.RequestWindows
import Airbender.Proofs.Blake2G.Windows
import Airbender.Proofs.Blake2Round.Windows
import Airbender.Proofs.Keccak.Windows

namespace Airbender.Delegation.Caller.Proofs
open Trace Reference.RiscV.Sail
variable {Kind : Type} [CircuitLayout Kind]
set_option warningAsError true

theorem bind_hash_window [Fact p.Prime] (hp : FieldCapacity.NativeWideHashCapacity p)
    (wordInverse : SerializedInverse.Scale64 p)
    (byteInverse : SerializedInverse.Scale256 p)
    {callers : List (Trace.Row p Kind)} {workers : MemoryData p} {before : State} {cells : List Cell}
    {span : HashSpan} {lower upper : Nat} (accepted : MemoryAccepted workers)
    (inputs : span.RequestWindowInputs workers before cells lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (binding : RequestWindowBinding callers workers lower upper) :
    span.RequestWindowResult callers workers before cells lower upper := by
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
  | blakeG reduced => exact Blake2G.Proofs.window_binding (by omega) wordInverse accepted inputs aligned
  | blakeRound flags => exact Blake2Round.Proofs.window_binding (by omega) wordInverse accepted inputs aligned
  | keccak => exact Keccak.Proofs.window_binding hp byteInverse accepted inputs aligned

end Airbender.Delegation.Caller.Proofs
