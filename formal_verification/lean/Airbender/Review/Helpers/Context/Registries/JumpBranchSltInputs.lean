import Airbender.Review.Helpers.Context.Registries.JumpBranchSlt
import Airbender.Review.Helpers.Context.Boundary
import Airbender.Review.Helpers.Decoder.Instruction

namespace Airbender.JumpBranchSlt
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Public initialization and logical protocol boundaries for this trace.
    No per-row operands, decoded instruction or expected result is supplied. -/
structure ExecutionBoundary {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) : Prop where
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  image : initialImage initial cells = some trace.initialMemory
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  initialAligned : trace.initial.word.lo % 4 = 0
  terminalCanonical : trace.terminal.word.Bounded
  programImage : ∃ addresses, JumpBranchSlt.programImage initial addresses = some program
  clocks : ClockBoundary trace
  misa : ∃ value, initial.regs.get? .misa = some value
  -- Machine mode and disabled landing pads are the admitted JALR configuration.
  indirect : initial.regs.get? .cur_privilege = some .Machine ∧
    ∃ security, initial.regs.get? .mseccfg = some security ∧
      SailRV32.Functions._get_Seccfg_MLPE security = 0

end Airbender.JumpBranchSlt
