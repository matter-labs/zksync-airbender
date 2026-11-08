module
public import Slop.Delegation.Operations
public import Slop.Trace.TransferBounds
public import Human.Helpers.Delegation.RequestEffects
public import Human.Helpers.Delegation.SharedMemory
public import Slop.Delegation.RequestTrace
public import Slop.Trace.TransferValues

@[expose] public section

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

end Airbender.Delegation.Caller.Proofs
