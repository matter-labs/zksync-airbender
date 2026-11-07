import Airbender.Review.Helpers.Context.Registries.MulDiv
import Airbender.Review.Helpers.Context.Boundary
import Airbender.Review.Helpers.Decoder.Instruction

namespace Airbender.MulDiv
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Public inputs and logical matching boundaries. Operand values, decoding,
    row results and terminal PC bounds are derived from the imported circuit. -/
abbrev ExecutionBoundary {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) :=
  NativeInputs decoderFields trace initial cells program

end Airbender.MulDiv
