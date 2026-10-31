import Airbender.Review.Circuits.Bigint.Call
import Airbender.Review.Circuits.Blake2G.Call
import Airbender.Review.Circuits.Blake2Round.Call
import Airbender.Review.Circuits.Keccak.Call

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail Reference.Sail

/-- Independent complete successful call effects, dispatched by the public CSR
    family. Each relation fixes actual reads, reference results and full frame. -/
def FullCall (family : Delegation.Family) : State → State → Prop :=
  match family with
  | .bigint => Bigint.Call.Executes
  | .blakeG => Blake2G.Call.Executes
  | .blakeRound => Blake2Round.Call.Executes
  | .keccak => Keccak.Call.Executes

def FullRetirement (family : Delegation.Family) (before after : State) : Prop :=
  ∃ middle, FullCall family before middle ∧
    run (do SailRV32.Functions.normal_base_next_pc (); SailRV32.Functions.tick_pc ()) middle = .ok () after

end Airbender.UnifiedReduced.Caller
