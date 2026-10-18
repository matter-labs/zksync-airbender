import Airbender.Review.Helpers.Decoder.Program
import Airbender.Review.Helpers.Memory.Platform

namespace Airbender.Trace
open Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Dispatch original Sail memory clauses or the shared register/control dispatcher.
    Unsupported instruction constructors have no execution clause. -/
def instructionClause : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)
  | .LOAD (imm, rs1, rd, unsigned, size) =>
    some (SailRV32.Functions.execute_LOAD imm rs1 rd unsigned size)
  | .STORE (imm, rs2, rs1, size) => some (SailRV32.Functions.execute_STORE imm rs2 rs1 size)
  | instruction => registerClause instruction

end Airbender.Trace
