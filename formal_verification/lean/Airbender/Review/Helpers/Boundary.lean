import Airbender.Review.Helpers.Program
import Airbender.Review.Helpers.ROM
import Airbender.Review.Helpers.Platform
import Airbender.Review.Helpers.Values

namespace Airbender.Trace
open Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Bind `trace`'s initial data to the public Sail state `initial` and tracked
    `cells`. `program` is constructed by reading public bytes and running Sail
    decoding, then projecting native metadata with `projection`.

    These are starting-state conditions. Accepted history derives later reads,
    operand bounds and decoder interfaces; callers do not supply those per row. -/
structure NativeInputs {Kind ISA : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime]
    (projection : SailRV32.instruction → Option (DecoderData ISA))
    (trace : Data p Kind) (initial : State) (cells : List Cell)
    (program : List (ProgramEntry ISA)) : Prop where
  /-- The public domain lists each tracked cell once. -/
  distinct : cells.Nodup
  /-- RAM entries are aligned four-byte cells; register cells need no alignment. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Reading the public starting state yields exactly the native seed tokens. -/
  image : initialImage initial cells = some trace.initialMemory
  /-- Sail's initial PC and a public timestamp form the native starting state. -/
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  /-- Public byte reads and actual Sail decoding construct every program entry. -/
  programImage : ∃ addresses, programImageRunWith projection initial addresses = some program
  /-- Only initial clock ranges/alignment are supplied; later clocks are proved. -/
  clocks : ClockBoundary trace

/-- Public machine configuration and address/program domain for the restricted
    arithmetic + word-memory trace. `initial` supplies Sail state and bytes;
    `cells` lists accessible tracked locations. This selects the supported normal
    memory path, without assuming that an instruction's access succeeds. -/
structure PublicBoundary (initial : State) (cells : List Cell)
    (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop where
  /-- All RV32 registers occur in the tracked domain, including x0. -/
  registers : ∀ index, Cell.register index ∈ cells
  /-- Each public tracked cell appears once. -/
  distinct : cells.Nodup
  /-- Tracked RAM cells are aligned words. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Tracked RAM excludes the platform's special MMIO windows. -/
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  /-- Public CSR/PMA/PMP settings select the supported Machine memory path. -/
  configuration : FlatMemoryConfiguration initial
  /-- The restricted program is fetched from public bytes and decoded by Sail. -/
  programImage : ∃ addresses, Trace.programImageWith projection initial addresses = some program
  /-- Instruction addresses lie in public ROM and are aligned to four bytes. -/
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0

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
