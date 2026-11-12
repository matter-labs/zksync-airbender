module
public import Human.Circuits.Blake2G.Protocol
public import Slop.Blake2Round.DiagonalG
public import Slop.Blake2Round.FinalXor
public import Slop.KernelRfl

@[expose] public section

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true

abbrev scheduledController (reduced : Bool) (i : Nat) (_bound : i < callCount reduced) : Control.Input :=
  controllerAt reduced i

end Airbender.Blake2G.Proofs
