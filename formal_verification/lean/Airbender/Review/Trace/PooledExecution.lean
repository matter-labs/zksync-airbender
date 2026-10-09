import Airbender.Review.Trace.PooledProgram
import Airbender.Review.Trace.Execution
import Airbender.Review.SubwordTables
import Airbender.Review.Trace.NativeMemory

namespace Airbender.Trace
open Reference.RiscV.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

abbrev PooledStep := StepWith pooledDecoderFields instructionClause

/-- Public normal-path conditions shared by physical and native boot images. -/
structure PooledPublicInputs (initial : State) (cells : List Cell)
    (program : List PooledProgramEntry) : Prop where
  registers : ∀ index, Cell.register index ∈ cells
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  configuration : FlatMemoryConfiguration initial
  landingPadDisabled : ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  loads : NoDiscardedLoads program

/-- Physical image binding. Operand/address ranges and actual reads are derived
    from accepted history; terminal-PC normalization is the jump/teardown boundary. -/
structure PooledInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry) : Prop
    extends NativeInputs pooledDecoderFields trace initial cells program,
      PooledPublicInputs initial cells program where
  wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  terminalPC : trace.terminal.word.Bounded

/-- The pinned zero-initialized native seed keeps ROM permutation values
    separate from physical bytes. Both modeled tables use the public byte image.
    This supplies initial data, never per-row bounds, reads or expected results. -/
structure PooledBootInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry) : Prop
    extends PooledPublicInputs initial cells program where
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  programImage : ∃ addresses, pooledProgramImage initial addresses = some program
  profile : InitialProfile initial cells
  seed : trace.initialMemory = ROMView.nativeBootImage cells
  initialBoundary : trace.initial = PCState.boundary 0 (4, 0)
  physicalImage : ∃ image, initialImage initial cells = some image ∧
    trace.rom.wordMemory = ROM.table cells image
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  terminalPC : trace.terminal.word.Bounded

end Airbender.Trace
