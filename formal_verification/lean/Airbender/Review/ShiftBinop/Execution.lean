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
abbrev ExecutionBoundary {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) :=
  NativeInputs decoderFields trace initial cells program

end Airbender.ShiftBinop
