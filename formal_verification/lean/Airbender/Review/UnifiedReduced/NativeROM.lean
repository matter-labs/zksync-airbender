import Airbender.Review.UnifiedReduced.Decoder
import Airbender.Review.UnifiedReduced.Setup
import Airbender.Review.Trace.NativeMemory

namespace Airbender.UnifiedReduced
open Trace Reference.RiscV.Sail

/-- Public boot inputs for native unified execution. Rust's ROM permutation
    slots start at zero; Sail's physical ROM keeps the public program bytes.
    Shared helpers connect these two views and derive later reads and bounds.
    Nothing here supplies an instruction's expected operands or result. -/
structure BootInputs [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
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
  programImage : ∃ addresses, UnifiedReduced.programImage initial addresses = some program
  /-- The modeled pooled table is fixed by the public physical ROM image. -/
  setup : trace.rom = Setup.table initial

end Airbender.UnifiedReduced
