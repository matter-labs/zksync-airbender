import Airbender.Review.Helpers.Context.Boundary
import Airbender.Review.Circuits.UnifiedReduced.Decoder
import Airbender.Review.Circuits.WordMemory.Model
import Airbender.Review.Helpers.Context.RowContext

namespace Airbender.UnifiedReduced.WordMemory
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace

/-- Unified LW/SW's canonical operands, effective address, data and PCs.
    Numbers live here; the trace interface below only names this mapping. -/
structure WordMapping (input : Airbender.WordMemory.Input) (output : Airbender.WordMemory.Output)
    (w : Nat → ZMod p) : Prop where
  sourceLo : input.source.lo = (w 36).val
  sourceHi : input.source.hi = (w 37).val
  immediateLo : input.immediate.lo = (w 8).val
  immediateHi : input.immediate.hi = (w 9).val
  readLo : input.readData.lo = (w 42).val
  readHi : input.readData.hi = (w 43).val
  addressLo : output.address.lo = (w (if input.store then 44 else 38)).val
  addressHi : output.address.hi = (w (if input.store then 45 else 39)).val
  dataLo : output.data.lo = (w 50).val
  dataHi : output.data.hi = (w 51).val
  pcLo : input.pc.lo = (w 0).val
  pcHi : input.pc.hi = (w 1).val
  finalPCLo : output.pc.lo = (w 30).val
  finalPCHi : output.pc.hi = (w 31).val

/-- Identify this assignment's position and original LOAD/STORE in the public
    image. The shared history supplies reads and bounds; these fields do not
    require either a successful memory access or a correct result. -/
structure TraceMapping [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (input : Airbender.WordMemory.Input) (output : Airbender.WordMemory.Output)
    (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  state : RowPosition trace initial cells ⟨.machine, w⟩ input.before
  instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
    entry.instruction = if input.store then
      .STORE (input.encodedImmediate, input.rs2, input.rs1, 4)
      else .LOAD (input.encodedImmediate, input.rs1, input.rd, false, 4)

/-- Public RAM profile for this first unified memory claim. Initialization
    binds actual Sail cells/program/clocks; configuration selects the reviewed
    Machine-mode memory path. Ordinary RAM cells exclude platform MMIO and
    start above ROM. Shared helpers derive all per-row ranges and access values.
    ROM loads and discarded LW writes have separate semantics and are excluded
    from this RAM claim. -/
structure InterfaceAssumptions [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (input : Airbender.WordMemory.Input) (_output : Airbender.WordMemory.Output)
    (_w : Nat → ZMod p) : Prop where
  initialization : NativeInputs decoderFields trace initial cells program
  configuration : FlatMemoryConfiguration initial
  ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address
  ram : ∀ address, Cell.ram address ∈ cells → 4194304 ≤ address.toNat
  destination : input.store = false → input.rd ≠ zeroRegister

/-- Imported equations, logical state/memory matching and actual decoder-table
    membership. Only the represented row must be LW/SW; other admitted unified
    instructions can supply its preceding state. -/
def circuitModel [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Airbender.WordMemory.Input Airbender.WordMemory.Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

end Airbender.UnifiedReduced.WordMemory
