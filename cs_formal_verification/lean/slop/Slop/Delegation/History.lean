module
public import Slop.Delegation.BoundaryInputs
public import Slop.OpIndex

@[expose] public section

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true

abbrev rawEvents (data : MemoryData p) := Trace.Proofs.Transfer.rawEvents (transferData data)
abbrev labeledEvents (data : MemoryData p) := Trace.Proofs.Transfer.labeledEvents (transferData data)

end Airbender.Delegation.Proofs
