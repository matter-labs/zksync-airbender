import Human.Helpers.Context.Boundary
import Human.Helpers.Context.FamilyLayout

namespace Airbender.Trace
open Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem

/-- Add physical memory, initial PC/clock and modeled-table binding to
    `PublicBoundary`. Here `trace.initialMemory` contains actual Sail cell values,
    including ROM bytes. Native zero ROM shadow tokens use `NativeBootBoundary`. -/
structure ExecutionBoundary {p : Nat} [Fact p.Prime] (trace : Data p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop
    extends PublicBoundary initial cells program projection where
  /-- Seed tokens contain the actual starting GPR and physical RAM/ROM values. -/
  image : initialImage initial cells = some trace.initialMemory
  /-- Bind the native starting PC and timestamp to the public state. -/
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  /-- Bind the modeled word-ROM table to these public physical values. -/
  rom : trace.rom = ROM.table cells trace.initialMemory
  /-- Supply the public initial-clock conditions needed by native matching. -/
  clocks : ClockBoundary trace

end Airbender.Trace
