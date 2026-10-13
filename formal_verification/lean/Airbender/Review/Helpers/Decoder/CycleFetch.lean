import Airbender.Review.Helpers.Decoder.Program
import Airbender.Review.Helpers.Memory.SailHistory

namespace Airbender.Trace

/-- Byte reads and original Sail decoding at an actual instruction-cycle PC.
    The entry comes from the public program and matches the native decoder query.
    Each possible pre-state of that same history sees those bytes/instruction;
    `reachable` shows such a pre-state exists. Platform fetch traps and whole
    instruction retirement are separate. -/
structure CycleFetch {NativeKind EntryKind : Type} [CircuitLayout NativeKind]
    (initial : Reference.RiscV.Sail.State) (cells : List Cell) (events : List MemoryAccess)
    (row : Row p NativeKind) (program : List (ProgramEntry EntryKind))
    (projection : SailRV32.instruction → Option (DecoderData EntryKind))
    (entryQuery : ProgramEntry EntryKind → Vector (ZMod p) 9) : Prop where
  /-- The initialized history reaches the boundary immediately before this cycle. -/
  reachable : ∃ before, SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before
  /-- The matched public entry is also read/decoded in every actual boundary state.
      PC/nextPC are set to the native cycle PC by the shared retirement view. -/
  instruction : ∃ entry ∈ program, row.decoderQuery = entryQuery entry ∧
    row.start.word.toBitVec = entry.pc ∧
    ∀ before, SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before →
      entry.SourceWith (retiredState before row.start.word.toBitVec) projection

end Airbender.Trace
