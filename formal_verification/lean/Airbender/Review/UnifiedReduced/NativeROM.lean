import Airbender.Review.UnifiedReduced.Decoder
import Airbender.Review.UnifiedReduced.Setup
import Airbender.Review.Trace.NativeMemory

namespace Airbender.UnifiedReduced
open Trace Reference.RiscV.Sail

/-- Public boot inputs for native unified execution, with the chosen metadata
    projection applied after original Sail decoding. Rust's ROM permutation
    slots start at zero; Sail's physical ROM keeps the public program bytes.
    Shared helpers connect these two views and derive later reads and bounds.
    Nothing here supplies an instruction's expected operands or result. -/
structure BootInputsWith (projection : SailRV32.instruction → Option (DecoderData UnifiedFamily))
    [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop where
  /-- Each tracked register or aligned RAM word occurs once. -/
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Initial PC/GPR/RAM values follow the pinned boot profile; ROM retains bytes. -/
  profile : InitialProfile initial cells
  /-- Actual initial cell reads succeed, including physical ROM reads. -/
  image : ∃ image : List (MemoryToken p), initialImage initial cells = some image
  /-- Native seed values are zero, independently of physical ROM bytes. -/
  seed : trace.initialMemory = Trace.ROMView.nativeBootImage cells
  /-- Public starting PC zero and native timestamp four. Later clocks are proved. -/
  initialPC : trace.initial = PCState.boundary 0 (4, 0)
  /-- Actual public bytes and original Sail decoding construct the program table. -/
  programImage : ∃ addresses, programImageRunWith projection initial addresses = some program
  /-- The modeled pooled table is fixed by the public physical ROM image. -/
  setup : trace.rom = Setup.table initial

/-- Standard public boot inputs use the standard native metadata projection. -/
abbrev BootInputs {p : Nat} [Fact p.Prime] := BootInputsWith (p := p) decoderFields

end Airbender.UnifiedReduced
