import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Review.Helpers.Context.Boundary
import Airbender.Review.Helpers.Decoder.Instruction
import Airbender.Review.Helpers.Tables.Subword
import Airbender.Review.Helpers.Memory.Native
import Airbender.Review.Helpers.Context.VerifierBoundary.Model

namespace Airbender.Trace
open Reference.RiscV.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public configuration and program domain shared by both six-family claims.
    `initial` is the starting Sail state, `cells` the tracked register/RAM domain,
    and `program` the public decoded entries. These conditions select the normal
    execution path; they supply no instruction read or result. -/
structure PooledPublicInputs (initial : State) (cells : List Cell)
    (program : List PooledProgramEntry) : Prop where
  /-- Every RV32 register, including x0, is in the public tracked domain. -/
  registers : ∀ index, Cell.register index ∈ cells
  /-- Tracked RAM avoids platform-specific MMIO windows. -/
  ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address
  /-- Public CSR/PMA/PMP values select the supported Machine memory path. -/
  configuration : FlatMemoryConfiguration initial
  /-- Disable JALR landing-pad updates, which the native circuit does not model. -/
  landingPadDisabled : ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  /-- Public instructions lie below the ROM limit at four-byte-aligned addresses. -/
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  /-- Exclude LW-to-x0, whose Airbender NOP behavior differs from unchanged Sail. -/
  loads : NoDiscardedLoads program

/-- Six-family execution from a physical initial image. `NativeInputs` binds
    public cells, code and clocks; `PooledPublicInputs` states configuration and
    program restrictions. These fields add modeled-table binding and the still
    external canonical verifier-boundary closure over raw PC-state tuples.

    Shared history proves individual operand/address ranges and actual reads.
    Use `PooledBootInputs` when native ROM tokens start at zero instead of bytes.
    `projection` selects standard or extended decoder metadata; both use actual Sail decoding. -/
structure PooledInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry)
    (projection : SailRV32.instruction → Option (DecoderData PooledFamily) := pooledDecoderFields) : Prop
    extends NativeInputs projection trace initial cells program,
      PooledPublicInputs initial cells program where
  /-- Word-memory lookup contents are modeled from the public physical seed. -/
  wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory
  /-- Subword ROM lookup contents use the starting Sail byte image. -/
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  /-- The typed statement closes the native PC-space permutation. Terminal
      bounds follow by canceling accepted state matching against this closure. -/
  verifierBoundary : VerifierBoundary.Closure trace.initial
    (trace.rows.map Row.start) (trace.rows.map Row.finish)

/-- Inputs to the primary standard and mixed execution claims. `initial` supplies
    public Sail state and program bytes; `cells` lists tracked registers/RAM.
    The native seed is zero, including ROM shadow tokens, while modeled ROM
    tables use the actual public bytes.

    Review the inherited configuration/program restrictions and these starting
    image bindings. Per-row bounds, reads and execution results are proved
    internally. The verifier closure uses the inspected initial PC/clock 0/4;
    its cryptographic enforcement and Rust/artifact correspondence stay external.
    `projection` selects standard or extended decoder metadata; both use actual Sail decoding. -/
structure PooledBootInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry)
    (projection : SailRV32.instruction → Option (DecoderData PooledFamily) := pooledDecoderFields) : Prop
    extends PooledPublicInputs initial cells program where
  /-- The public domain has no repeated cells. -/
  distinct : cells.Nodup
  /-- Tracked RAM cells are aligned words. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Read public code bytes and run pinned Sail decoding for all program entries. -/
  programImage : ∃ addresses, programImageRunWith projection initial addresses = some program
  /-- Sail starts at PC zero with zero GPRs and zero tracked non-ROM RAM. -/
  profile : InitialProfile initial cells
  /-- All native seed values and prior timestamps are zero, including ROM shadow slots. -/
  seed : trace.initialMemory = ROMView.nativeBootImage cells
  /-- The native machine starts at PC zero and clock four. -/
  initialBoundary : trace.initial = PCState.boundary 0 (4, 0)
  /-- Read actual Sail cell values and bind the modeled word-ROM table to that image. -/
  physicalImage : ∃ image, initialImage initial cells = some image ∧
    trace.rom.wordMemory = ROM.table cells image
  /-- Bind subword ROM lookups to public bytes, independently of zero shadow tokens. -/
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  /-- Typed total-verifier closure with initial PC zero and timestamp four.
      No raw terminal-PC range is supplied. -/
  verifierBoundary : VerifierBoundary.BootClosure trace.initial
    (trace.rows.map Row.start) (trace.rows.map Row.finish)

end Airbender.Trace
