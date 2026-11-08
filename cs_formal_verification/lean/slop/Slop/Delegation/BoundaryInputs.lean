import Human.Helpers.Delegation.Memory
import Human.Helpers.Delegation.Operations
import Slop.Trace.TransferBoundary

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs
set_option warningAsError true

def transferData (data : MemoryData p) : Transfer.Data p :=
  ⟨data.initial, data.terminal, data.steps⟩

end Airbender.Delegation.Proofs

namespace Airbender.Delegation
open Trace

end Airbender.Delegation
