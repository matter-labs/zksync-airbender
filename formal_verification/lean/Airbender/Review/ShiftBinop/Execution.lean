import Airbender.Review.ShiftBinop.Trace
import Airbender.Review.Trace.Execution

namespace Airbender.ShiftBinop
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Original Sail fetch/decoding, execution and retirement, using the same
    step relation as the arithmetic/memory and jump-family traces. -/
abbrev SailStep := StepWith decoderFields Trace.instructionClause
abbrev SailTrace (program : List ProgramEntry) := Relation.ReflTransGen (SailStep program)

/-- Public inputs and logical matching boundaries. Operand values, decoding,
    row results and terminal PC bounds are derived from the imported circuit. -/
structure ExecutionBoundary {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) : Prop where
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  image : initialImage initial cells = some trace.initialMemory
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  programImage : ∃ addresses, ShiftBinop.programImage initial addresses = some program
  clocks : ClockBoundary trace

end Airbender.ShiftBinop
