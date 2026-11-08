import Slop.Trace.TransferBounds
import Slop.Trace.TransferSplit

namespace Airbender.Trace.Proofs.Transfer
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

def windowSteps (data : Data p) (lower upper : Nat) :=
  beforeSteps ⟨data.initial, data.terminal, afterSteps data lower⟩ upper

end Airbender.Trace.Proofs.Transfer
