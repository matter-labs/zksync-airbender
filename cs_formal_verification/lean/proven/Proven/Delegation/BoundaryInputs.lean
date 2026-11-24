module
public import Human.Helpers.Delegation.Memory
public import Proven.Trace.TransferHistory

@[expose] public section

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs
set_option warningAsError true

def transferData (data : MemoryData p) : Transfer.Data p :=
  ⟨data.initial, data.terminal, data.steps⟩

end Airbender.Delegation.Proofs

namespace Airbender.Delegation
open Trace

end Airbender.Delegation
