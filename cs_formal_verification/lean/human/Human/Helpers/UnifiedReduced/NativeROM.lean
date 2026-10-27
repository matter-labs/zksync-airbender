import Human.Circuits.UnifiedReduced.Decoder
import Human.Circuits.UnifiedReduced.Tables.Setup
import Human.Helpers.Memory.Native

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
  programImage : ∃ addresses, programImageWith projection initial addresses = some program
  /-- The modeled pooled table is fixed by the public physical ROM image. -/
  setup : trace.rom = Setup.table initial
  /-- The Airbender machine's configuration (`Configured`). -/
  configuration : Reference.RiscV.Sail.Configured initial

/-- Standard public boot inputs use the standard native metadata projection. -/
abbrev BootInputs {p : Nat} [Fact p.Prime] := BootInputsWith (p := p) decoderFields

end Airbender.UnifiedReduced

namespace Airbender.UnifiedReduced.ROMView
open Trace Arithmetic Reference.RiscV.Sail

/-- Replace the native ROM read limbs and their unused product column. -/
def readData (w : Nat → ZMod p) (lo hi : ZMod p) : Nat → ZMod p :=
  fun i => if i = 42 then lo else if i = 43 then hi else if i = 80 then
    (w 36 + 65536 * w 37) * (lo + 65536 * hi) * 943718400 + (w 48 + 65536 * w 49) * w 17
    else w i

/-- Interpret a selected native ROM load using actual public program bytes. -/
def row (before : Reference.RiscV.Sail.State) (native : Trace.Row p UnifiedFamily) : Trace.Row p UnifiedFamily :=
  if native.assignment 28 = 1 ∧ native.assignment 54 = 1 then
    let word := Trace.ROMView.publicWord before
      (Nat.pair 1 (Nat.pair (native.assignment 38).val (native.assignment 39).val))
    { native with assignment := readData native.assignment word.lo word.hi }
  else native

/-- Replace native ROM data with public words while retaining clocks and endpoints. -/
def data [Fact p.Prime] (before : State) (native : UnifiedTrace p) : UnifiedTrace p :=
  { native with rows := native.rows.map (row before)
                initialMemory := native.initialMemory.map (Trace.ROMView.token before)
                terminalMemory := native.terminalMemory.map (Trace.ROMView.token before) }

end Airbender.UnifiedReduced.ROMView
