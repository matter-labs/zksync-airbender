import Human.Trace.Workers.Keccak.Call
import CleanCore.Specs.Keccak256
import Human.Helpers.Delegation.WorkerContext

namespace Airbender.Keccak.Permutation
open Trace

/-- Byte offset of one logical Clean lane in Airbender's row-major RAM block.
    Clean numbers lanes column-first; each physical lane occupies eight bytes. -/
def laneOffset (lane : Fin 25) : Nat := 8 * (lane.val / 5 + 5 * (lane.val % 5))

end Airbender.Keccak.Permutation
