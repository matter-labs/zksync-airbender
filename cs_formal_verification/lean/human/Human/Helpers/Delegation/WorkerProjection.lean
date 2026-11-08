module
public import Human.Helpers.Delegation.SharedMemory

@[expose] public section

namespace Airbender.Delegation
open Trace

/-- Keep the actual workers and derive their non-x0 boundaries from the shared
    architecture. The caller-only projection proof justifies removing x0. -/
def MemoryData.workerProjection (workers : MemoryData p)
    (initial terminal : List (MemoryToken p)) : MemoryData p :=
  { workers with
    initial := initial.filter fun token => token.address != (Cell.register 0).addressCode
    terminal := terminal.filter fun token => token.address != (Cell.register 0).addressCode }

end Airbender.Delegation

namespace Airbender.Delegation.Caller
open Trace

/-- The public worker cell domain. Decoded callers touch only x0; none of the
    four native worker layouts touches it. This projection removes that one
    cell and retains all worker GPR/RAM addresses. -/
def workerCells (cells : List Cell) :=
  cells.filter fun cell => cell.addressCode != (Cell.register 0).addressCode

end Airbender.Delegation.Caller
