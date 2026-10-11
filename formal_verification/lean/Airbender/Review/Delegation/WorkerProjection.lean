import Airbender.Review.Delegation.SharedMemory

namespace Airbender.Delegation.Caller
open Trace

/-- The public worker cell domain. Decoded callers touch only x0; none of the
    four native worker layouts touches it. This projection removes that one
    cell and retains all worker GPR/RAM addresses. -/
def workerCells (cells : List Cell) :=
  cells.filter fun cell => cell.addressCode != (Cell.register 0).addressCode

/-- The same native workers with boundary tokens derived from shared matching.
    Original worker-only seed/terminal tokens are unused. This projection is
    valid for the caller-only scope; ordinary ISA rows can update worker cells
    and require the subsequent mixed-machine history. -/
def RequestTrace.workerProjection [Fact p.Prime] (data : RequestTrace p) : MemoryData p :=
  { data.workers with
    initial := data.machine.initialMemory.filter fun token =>
      token.address != (Cell.register 0).addressCode
    terminal := data.machine.terminalMemory.filter fun token =>
      token.address != (Cell.register 0).addressCode }

end Airbender.Delegation.Caller
