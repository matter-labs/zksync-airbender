import Airbender.Review.Trace.Program
import Airbender.Review.Trace.ROM
import Airbender.Review.Trace.Platform
import Mathlib.Logic.Relation

namespace Airbender.Trace
open Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
variable [MemoryPlatform SailRV32.exception]

/-- Dispatch to the original generated Sail clauses, without defining any
    instruction behavior. Unsupported constructors have no clause here. -/
def instructionClause : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult)
  | .RTYPE (rs2, rs1, rd, .ADD) => some (SailRV32.Functions.execute_RTYPE rs2 rs1 rd .ADD)
  | .RTYPE (rs2, rs1, rd, .SUB) => some (SailRV32.Functions.execute_RTYPE rs2 rs1 rd .SUB)
  | .ITYPE (imm, rs1, rd, .ADDI) => some (SailRV32.Functions.execute_ITYPE imm rs1 rd .ADDI)
  | .UTYPE (imm, rd, .LUI) => some (SailRV32.Functions.execute_UTYPE imm rd .LUI)
  | .UTYPE (imm, rd, .AUIPC) => some (SailRV32.Functions.execute_UTYPE imm rd .AUIPC)
  | .LOAD (imm, rs1, rd, false, 4) =>
    some (SailRV32.Functions.execute_LOAD imm rs1 rd false 4)
  | .STORE (imm, rs2, rs1, 4) => some (SailRV32.Functions.execute_STORE imm rs2 rs1 4)
  | _ => none

/-- One successful normal instruction: current public code bytes, original
    Sail decoding, and the original preparation/execution/retirement clauses. -/
def SailStep (program : List ProgramEntry) (before after : State) : Prop :=
  ∃ entry ∈ program, entry.Source before ∧
    run (SailRV32.Functions.get_arch_pc ()) before = .ok entry.pc before ∧
    ∃ clause, instructionClause entry.instruction = some clause ∧
      run (normalStep clause) before = .ok SailRV32.Functions.RETIRE_SUCCESS after

/-- A finite sequence of the checked Sail steps, including an empty trace. -/
abbrev SailTrace (program : List ProgramEntry) := Relation.ReflTransGen (SailStep program)

/-- Current scope restriction: LW-to-x0's ignored memory access is not yet
    justified by native NOP rows. Arithmetic writes to x0 remain covered. -/
def NoDiscardedLoads (program : List ProgramEntry) : Prop :=
  ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

/-- Public initial data, configuration and normal-path code/domain conditions.
    Logical state/memory matching and decoder membership are separate inputs;
    no instruction read, decoded result, or final value is assumed here. -/
structure ExecutionBoundary {p : Nat} [Fact p.Prime] (trace : Data p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) : Prop where
  image : initialImage initial cells = some trace.initialMemory
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  rom : trace.rom = ROM.table cells trace.initialMemory
  registers : ∀ index, Cell.register index ∈ cells
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  configuration : FlatMemoryConfiguration initial
  programImage : ∃ addresses, Trace.programImage initial addresses = some program
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0
  clocks : ClockBoundary trace

end Airbender.Trace
