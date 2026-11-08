import Slop.Blake2G.State
import Slop.Blake2G.NativeExecution
import Slop.Blake2G.BlockFrame
import Slop.Blake2Round.Compression
import Slop.Blake2Round.StateTransport

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def stateLanes (controller : Control.Input) : Vector (Fin 16) 4 :=
  Vector.ofFn fun i => ⟨(Control.step controller).stateOffsets[i],
    Control.Proofs.state_offsets_bounded controller i⟩

end Airbender.Blake2G.Proofs
