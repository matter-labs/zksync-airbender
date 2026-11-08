module
public import Slop.Blake2G.State
public import Slop.Blake2G.NativeExecution
public import Slop.Blake2G.BlockFrame
public import Slop.Blake2Round.Compression
public import Slop.Blake2Round.StateTransport

@[expose] public section

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

def stateLanes (controller : Control.Input) : Vector (Fin 16) 4 :=
  Vector.ofFn fun i => ⟨(Control.step controller).stateOffsets[i],
    Control.Proofs.state_offsets_bounded controller i⟩

end Airbender.Blake2G.Proofs
