import Human.Helpers.Decoder.RVProgram
import Human.Helpers.Memory.InitialImageRV
import Human.Helpers.Context.Model

/-! RV-typed sibling of `NativeInputs` (`Boundary.lean`): the public starting point is an `RV.State`. No `Configured`
    premise: the RV spec has no configuration state. Program entries are the RV table (`rvProgramImageWith`). -/

namespace Airbender.Trace

/-- Bind `trace`'s initial data to the public RV starting state `initial` and tracked `cells`. `program` is built by
    `rvProgramImageWith`: public bytes read by `RV.read`, decoded by `RV.decode`, then projected to native metadata. -/
structure RVNativeInputs {Kind ISA : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime]
    (projection : RV.Instr → Option (DecoderData ISA))
    (trace : Data p Kind) (initial : RV.State) (cells : List Cell)
    (program : List (RVProgramEntry ISA)) : Prop where
  /-- The public domain lists each tracked cell once. -/
  distinct : cells.Nodup
  /-- RAM entries are aligned four-byte cells; register cells need no alignment. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Reading the public starting state yields exactly the native seed tokens. -/
  image : initialImageRV initial cells = some trace.initialMemory
  /-- The starting PC and a public timestamp form the native starting state. -/
  initialPC : ∃ timestamp, initialStateRV initial timestamp = trace.initial
  /-- Public byte reads and RV decoding construct every program entry. -/
  programImage : ∃ addresses, rvProgramImageWith projection initial addresses = some program
  /-- Only initial clock ranges/alignment are supplied; later clocks are proved. -/
  clocks : ClockBoundary trace

end Airbender.Trace
