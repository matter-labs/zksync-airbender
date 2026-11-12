module
public import Human.Helpers.Context.RVBoundary
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.Helpers.Memory.ROM
public import Human.Helpers.Tables.Subword

@[expose] public section

namespace Airbender.Trace

/-- Public context shared by per-row claims, with the starting state an
    `RV.State`. Initialization fixes the starting state and program; the two modeled ROM tables use that same state. -/
structure RVPooledHistoryInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop where
  /-- Public cell values, starting PC/clocks and RV-decoded program. -/
  initialization : RVNativeInputs rvPooledDecoderFields trace initial cells program
  /-- Modeled word-ROM queries hold the ROM image's words at the public ROM cells. -/
  wordTable : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells)
  /-- Modeled subword ROM queries refer to the same ROM image. -/
  subwordTable : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial)

end Airbender.Trace
