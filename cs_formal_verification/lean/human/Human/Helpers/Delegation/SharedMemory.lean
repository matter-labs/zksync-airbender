import Human.Helpers.Context.Registries.Pooled
import Human.Helpers.Delegation.Decoder
import Human.Helpers.Delegation.WorkerContext

namespace Airbender.Delegation.Caller
open Trace

/-- The two architectural caller ports: rs1 and rd. The intervening full-width
    CSR port belongs to the request permutation, so it is excluded from GPR/RAM
    matching. Placements come from the imported ADD/SUB descriptors. -/
def architecturalPorts : Array MemoryPort :=
  #[AddSub.importedConstraintsMemoryPorts[0], AddSub.importedConstraintsMemoryPorts[2]]

def architecturalSteps (w : Nat → ZMod p) : List (MemoryToken p × MemoryToken p) :=
  architecturalPorts.toList.map fun port =>
    (readToken w port, writeToken AddSub.importedConstraintsTraceColumns w port)

end Airbender.Delegation.Caller
