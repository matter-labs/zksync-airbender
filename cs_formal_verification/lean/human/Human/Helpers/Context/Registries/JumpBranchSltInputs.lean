import Human.Helpers.Context.Registries.JumpBranchSlt
import Human.Helpers.Context.Boundary
import Human.Helpers.Decoder.Instruction

namespace Airbender.JumpBranchSlt
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem

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
  /-- The Airbender machine's configuration (`Configured`). -/
  configuration : Configured initial

end Airbender.JumpBranchSlt
