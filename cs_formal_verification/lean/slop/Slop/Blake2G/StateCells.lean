module
public import Slop.Blake2G.PhysicalPorts
public import Slop.Delegation.Operations
public import Slop.Blake2G.ControlPool

@[expose] public section

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true

abbrev scheduledController (reduced : Bool) (i : Nat) (_bound : i < callCount reduced) : Control.Input :=
  controllerAt reduced i

end Airbender.Blake2G.Proofs
