import Airbender.Review.Helpers.Context.Registries.SubwordMemory
import Airbender.Review.Helpers.Tables.Subword
import Airbender.Review.Helpers.Context.Boundary
import Airbender.Review.Helpers.Decoder.Instruction

namespace Airbender.SubwordMemory
open Trace Reference.RiscV.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- RAM-only normal execution. The public initialized RAM domain lies outside
    ROM and device windows. No per-row operand bound, read or result is assumed.
    ROM loads will use the separate public-byte/shadow binding. -/
structure RAMInputs {p : Nat} [Fact p.Prime] (trace : NativeTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) : Prop
    extends NativeInputs decoderFields trace initial cells program where
  configuration : FlatMemoryConfiguration initial
  ramDomain : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  setup : ∃ values, trace.rom = Verification.subwordTable values

end Airbender.SubwordMemory
