import Airbender.Review.Helpers.Delegation.Memory
import Airbender.Review.Helpers.Memory.Native

namespace Airbender.ExternalBoundary.WorkerRAM
open Trace

/-- The project's successful-call domain: GPRs or physical RAM above ROM.
    The actual call ABI/refinement must authenticate this location for each
    native port; an opcode or virtual request alone does not establish it. -/
inductive Location where
  | register (index : BitVec 5)
  | ram (address : BitVec 32) (outside : ROM.limit ≤ address.toNat)

def Location.cell : Location → Cell
  | .register index => .register index
  | .ram address _ => .ram address

/-- Temporary restriction for the open F04 native-ROM/reference gap, not a
    property derived from arbitrary native acceptance or a fix to its encoding.
    Full native address-code binding for every worker port, including fixed
    registers and every indirect block word. It supplies no read/write value. -/
def Binding (workers : List (Delegation.Row p)) : Prop :=
  ∀ row ∈ workers, ∀ port ∈ row.ports, ∃ location : Location,
    port.address.code row.assignment = location.cell.addressCode

end Airbender.ExternalBoundary.WorkerRAM
