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
  | .RTYPE (rs2, rs1, rd, opcode) => some (SailRV32.Functions.execute_RTYPE rs2 rs1 rd opcode)
  | .ITYPE (imm, rs1, rd, opcode) => some (SailRV32.Functions.execute_ITYPE imm rs1 rd opcode)
  | .SHIFTIOP (amount, rs1, rd, opcode) =>
    some (SailRV32.Functions.execute_SHIFTIOP amount rs1 rd opcode)
  | .REV8 (rs1, rd) => some (SailRV32.Functions.execute_REV8 rs1 rd)
  | .UTYPE (imm, rd, .LUI) => some (SailRV32.Functions.execute_UTYPE imm rd .LUI)
  | .UTYPE (imm, rd, .AUIPC) => some (SailRV32.Functions.execute_UTYPE imm rd .AUIPC)
  | .LOAD (imm, rs1, rd, unsigned, size) =>
    some (SailRV32.Functions.execute_LOAD imm rs1 rd unsigned size)
  | .STORE (imm, rs2, rs1, size) => some (SailRV32.Functions.execute_STORE imm rs2 rs1 size)
  | .BTYPE (imm, rs2, rs1, opcode) => some (SailRV32.Functions.execute_BTYPE imm rs2 rs1 opcode)
  | .JAL (imm, rd) => some (SailRV32.Functions.execute_JAL imm rd)
  | .JALR (imm, rs1, rd) => some (SailRV32.Functions.execute_JALR imm rs1 rd)
  | .MUL (rs2, rs1, rd, opcode) => some (SailRV32.Functions.execute_MUL rs2 rs1 rd opcode)
  | .DIV (rs2, rs1, rd, unsigned) => some (SailRV32.Functions.execute_DIV rs2 rs1 rd unsigned)
  | .REM (rs2, rs1, rd, unsigned) => some (SailRV32.Functions.execute_REM rs2 rs1 rd unsigned)
  | _ => none

inductive ISAProfile where
  | sail
  | airbender

/-- The pinned Airbender ISA table makes LW-to-x0 a PC-only NOP, even for
    unaligned addresses (`vendor/airbender/00-master.md`, LW row). Implement
    that one deviation with the original Sail ADDI x0,x0,0 clause. All other
    selected instructions execute their unchanged original Sail clauses. -/
def profileClause (profile : ISAProfile) (instruction : SailRV32.instruction) :
    Option (SailRV32.SailM SailRV32.ExecutionResult) :=
  match profile, instruction with
  | .airbender, .LOAD (_, _, .Regidx 0, false, 4) =>
    some (SailRV32.Functions.execute_ITYPE 0 (.Regidx 0) (.Regidx 0) .ADDI)
  | _, _ => instructionClause instruction

/-- One successful normal instruction: current public code bytes, original
    Sail decoding, and Sail preparation/execution/retirement. `profile`
    explicitly selects unchanged Sail or the documented Airbender deviation. -/
def StepWith {Kind : Type}
    (projection : SailRV32.instruction → Option (DecoderData Kind))
    (clauseFor : SailRV32.instruction → Option (SailRV32.SailM SailRV32.ExecutionResult))
    (program : List (ProgramEntry Kind)) (before after : State) : Prop :=
  ∃ entry ∈ program, entry.SourceWith before projection ∧
    run (SailRV32.Functions.get_arch_pc ()) before = .ok entry.pc before ∧
    ∃ clause, clauseFor entry.instruction = some clause ∧
      run (normalStep clause) before = .ok SailRV32.Functions.RETIRE_SUCCESS after

abbrev Step (profile : ISAProfile) := StepWith decoderFields (profileClause profile)

/-- A finite sequence of the checked Sail steps, including an empty trace. -/
abbrev ExecutionTrace (profile : ISAProfile) (program : List ProgramEntry) :=
  Relation.ReflTransGen (Step profile program)

abbrev SailStep := Step .sail
abbrev SailTrace := ExecutionTrace .sail
abbrev AirbenderTrace := ExecutionTrace .airbender

/-- Current scope restriction: LW-to-x0's ignored memory access is not yet
    justified by native NOP rows. Arithmetic writes to x0 remain covered. -/
def NoDiscardedLoads (program : List ProgramEntry) : Prop :=
  ∀ entry ∈ program, ∀ (imm : BitVec 12) (rs1 : BitVec 5),
    entry.instruction ≠ .LOAD (imm, .Regidx rs1, .Regidx 0, false, 4)

/-- Shared public initialization for native traces. Cell values and instruction
    metadata are extracted from Sail; operand bounds are proved from history. -/
structure NativeInputs {Kind ISA : Type} [CircuitLayout Kind]
    {p : Nat} [Fact p.Prime]
    (projection : SailRV32.instruction → Option (DecoderData ISA))
    (trace : Data p Kind) (initial : State) (cells : List Cell)
    (program : List (ProgramEntry ISA)) : Prop where
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  image : initialImage initial cells = some trace.initialMemory
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  programImage : ∃ addresses, programImageRunWith projection initial addresses = some program
  clocks : ClockBoundary trace

/-- Public configuration, address domain and normal-path program conditions,
    shared by general-state and native zero-initialized execution. -/
structure PublicBoundary (initial : State) (cells : List Cell)
    (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop where
  registers : ∀ index, Cell.register index ∈ cells
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  ordinary : ∀ address, Cell.ram address ∈ cells → OrdinaryWordAddress address
  configuration : FlatMemoryConfiguration initial
  programImage : ∃ addresses, Trace.programImageWith projection initial addresses = some program
  code : ∀ entry ∈ program, entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0

/-- Physical Sail memory image and initial PC/clock binding. Native ROM
    permutation slots use the separate zero-initialized boundary below. -/
structure ExecutionBoundary {p : Nat} [Fact p.Prime] (trace : Data p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop
    extends PublicBoundary initial cells program projection where
  image : initialImage initial cells = some trace.initialMemory
  initialPC : ∃ timestamp, initialState initial timestamp = some trace.initial
  rom : trace.rom = ROM.table cells trace.initialMemory
  clocks : ClockBoundary trace

end Airbender.Trace
