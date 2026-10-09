import Airbender.Review.Trace.PooledProgram
import Airbender.Review.Trace.Execution
import Airbender.Review.SubwordTables

namespace Airbender.Trace
open Reference.RiscV.Sail
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

abbrev PooledStep := StepWith pooledDecoderFields instructionClause

/-- Public initial data, normal-path configuration and modeled setup binding.
    Operand/address ranges and actual reads are consequences of accepted history.
    Terminal-PC normalization is the remaining jump/teardown boundary. -/
structure PooledInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry) : Prop
    extends NativeInputs pooledDecoderFields trace initial cells program where
  registers : ∀ index, Cell.register index ∈ cells
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  configuration : FlatMemoryConfiguration initial
  landingPadDisabled : ∃ security, initial.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  loads : NoDiscardedLoads program
  wordSetup : trace.rom.wordMemory = ROM.table cells trace.initialMemory
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)
  terminalPC : trace.terminal.word.Bounded

end Airbender.Trace
