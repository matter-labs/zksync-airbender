module
public import Slop.Blake2G.Control
public import Slop.Blake2Round.DiagonalG
public import Slop.Blake2Round.FinalXor
public import Slop.KernelRfl
public import Batteries.Data.Fin.Fold

@[expose] public section

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

def stateLanes (controller : Control.Input) : Vector (Fin 16) 4 :=
  Vector.ofFn fun i => ⟨(Control.step controller).stateOffsets[i],
    Control.Proofs.state_offsets_bounded controller i⟩

end Airbender.Blake2G.Proofs
