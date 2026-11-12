module
public import Slop.Trace.TransferBounds
public import Slop.Trace.TransferSplit

@[expose] public section

namespace Airbender.Trace.Proofs.Transfer
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

def windowSteps (data : Data p) (lower upper : Nat) :=
  beforeSteps ⟨data.initial, data.terminal, afterSteps data lower⟩ upper

end Airbender.Trace.Proofs.Transfer
