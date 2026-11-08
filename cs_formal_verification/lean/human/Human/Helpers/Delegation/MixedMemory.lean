import Human.Helpers.Decoder.PooledProgram
import Human.Helpers.Memory.ROM
import Human.Helpers.Tables.Subword
import Human.Helpers.Delegation.RequestEffects
import Human.Helpers.Delegation.SharedMemory

namespace Airbender.Delegation.Caller
open Trace

/-- Architectural ports of a participating machine row. Ordinary rows keep all
    native ports; a selected caller excludes its virtual CSR request port. The
    selector is read from the assignment and checked against public decoding. -/
def machinePorts (row : Trace.Row p PooledFamily) : Array MemoryPort :=
  if row.family == .addSub && decide (Requests.Selected row.assignment) then
    architecturalPorts else row.ports

end Airbender.Delegation.Caller
