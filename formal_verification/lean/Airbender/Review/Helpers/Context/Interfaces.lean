import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Review.Helpers.Context.Boundary
import Airbender.Review.Helpers.Memory.ROM
import Airbender.Review.Helpers.Tables.Subword

namespace Airbender.Trace
open Reference.RiscV.Sail

/-- Public context shared by per-row claims in the six-family trace.
    Initialization fixes the starting Sail state and program; the two modeled
    ROM tables use that same state. This supplies no later reads or word bounds. -/
structure PooledHistoryInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry) : Prop where
  /-- Public cell values, starting PC/clocks and actual Sail-decoded program. -/
  initialization : NativeInputs pooledDecoderFields trace initial cells program
  /-- Modeled word-ROM queries refer to the public initialized cells. -/
  wordTable : trace.rom.wordMemory = ROM.table cells trace.initialMemory
  /-- Modeled subword ROM queries refer to the same public byte image. -/
  subwordTable : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)

end Airbender.Trace
