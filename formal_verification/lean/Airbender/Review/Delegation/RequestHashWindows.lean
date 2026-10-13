import Airbender.Review.Delegation.RequestWindows
import Airbender.Review.Blake2G.Windows
import Airbender.Review.Blake2Round.Windows
import Airbender.Review.Keccak.Windows

namespace Airbender.Delegation.Caller
open Trace Reference.RiscV.Sail
variable {Kind : Type} [CircuitLayout Kind]

/-- The existing native-window ABI: repeated G spans in one mode, or the first
    extended-BLAKE/Keccak span. Public controls and modeled tables remain explicit. -/
def HashSpan.RequestWindowInputs [Fact p.Prime] (span : HashSpan) (workers : MemoryData p)
    (before : State) (cells : List Cell) (lower upper : Nat) : Prop :=
  match span with
  | .blakeG reduced => Blake2G.WindowInputs workers before cells reduced lower upper
  | .blakeRound flags => Blake2Round.WindowInputs workers before cells flags lower upper
  | .keccak => Keccak.WindowInputs workers before cells lower upper

/-- Actual decoded caller requests and the complete hash reference use the same
    selected native worker rows. This retains worker-only memory matching;
    joint mixed-ISA retirement and caller control preparation remain separate. -/
structure HashSpan.RequestWindowResult [Fact p.Prime] (span : HashSpan)
    (callers : List (Trace.Row p Kind)) (workers : MemoryData p)
    (before : State) (cells : List Cell) (lower upper : Nat) : Prop extends
      RequestWindowBinding callers workers lower upper where
  /-- The complete pinned hash reference at history-derived Sail cut states. -/
  reference : span.WindowResult workers before cells lower upper
  /-- The worker-span ABI derives the number of actual caller instructions. -/
  count : (windowCallers callers lower upper).length = span.callCount
  /-- Every selected caller uses this protocol's full-width CSR. -/
  family : ∀ caller ∈ windowCallers callers lower upper,
    (Requests.caller caller.assignment).csr = Requests.csr span.family

end Airbender.Delegation.Caller
