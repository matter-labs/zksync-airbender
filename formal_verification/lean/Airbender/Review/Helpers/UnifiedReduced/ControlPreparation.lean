import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.UnifiedReduced.Windows

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Original Sail instructions that write a public constant from x0 or a U-immediate. -/
inductive ControlLiteral where
  | addi (immediate : BitVec 12)
  | lui (immediate : BitVec 20)

def ControlLiteral.instruction (literal : ControlLiteral) (register : BitVec 5) : SailRV32.instruction :=
  match literal with
  | .addi immediate => .ITYPE (immediate, .Regidx 0, .Regidx register, .ADDI)
  | .lui immediate => .UTYPE (immediate, .Regidx register, .LUI)

/-- The same original Sail sign extension and U-immediate packing used by decoding. -/
def ControlLiteral.value : ControlLiteral → BitVec 32
  | .addi immediate => SailRV32.Functions.sign_extend (m := 32) immediate
  | .lui immediate => immediate ++ (0 : BitVec 12)

/-- An ordinary registry of public constant writes; callers are registered separately. -/
def LiteralProgram (program : List UnifiedReduced.ProgramEntry) : Prop :=
  ∀ entry ∈ program, ∃ (register : BitVec 5) (literal : ControlLiteral),
    register ≠ (0 : BitVec 5) ∧ entry.instruction = literal.instruction register

/-- Original arithmetic forms that advance PC by four. Operands and results are
    unrestricted; actual decoding and accepted constraints supply their effects. -/
inductive ArithmeticInstruction : SailRV32.instruction → Prop where
  | add (rs2 rs1 rd : BitVec 5) : ArithmeticInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD))
  | sub (rs2 rs1 rd : BitVec 5) : ArithmeticInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB))
  | addi (imm : BitVec 12) (rs1 rd : BitVec 5) : ArithmeticInstruction (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI))
  | lui (imm : BitVec 20) (rd : BitVec 5) : ArithmeticInstruction (.UTYPE (imm, .Regidx rd, .LUI))
  | auipc (imm : BitVec 20) (rd : BitVec 5) : ArithmeticInstruction (.UTYPE (imm, .Regidx rd, .AUIPC))

/-- Public ADD/SUB/ADDI/LUI/AUIPC registry, including nonliteral writes and x0. -/
def ArithmeticProgram (program : List UnifiedReduced.ProgramEntry) : Prop :=
  ∀ entry ∈ program, ArithmeticInstruction entry.instruction

/-- Public instruction forms using the native PC-increment path. Successful
    public decoding still checks destinations, shift payloads and MOP numbers. -/
inductive SequentialInstruction : SailRV32.instruction → Prop where
  | arithmetic {instruction} (supported : ArithmeticInstruction instruction) : SequentialInstruction instruction
  | lw (imm : BitVec 12) (rs1 rd : BitVec 5) : SequentialInstruction (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 4))
  | sw (imm : BitVec 12) (rs2 rs1 : BitVec 5) : SequentialInstruction (.STORE (imm, .Regidx rs2, .Regidx rs1, 4))
  | xor (rs2 rs1 rd : BitVec 5) : SequentialInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .XOR))
  | or (rs2 rs1 rd : BitVec 5) : SequentialInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR))
  | and (rs2 rs1 rd : BitVec 5) : SequentialInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND))
  | sll (rs2 rs1 rd : BitVec 5) : SequentialInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLL))
  | srl (rs2 rs1 rd : BitVec 5) : SequentialInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRL))
  | sra (rs2 rs1 rd : BitVec 5) : SequentialInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRA))
  | xori (imm : BitVec 12) (rs1 rd : BitVec 5) : SequentialInstruction (.ITYPE (imm, .Regidx rs1, .Regidx rd, .XORI))
  | ori (imm : BitVec 12) (rs1 rd : BitVec 5) : SequentialInstruction (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI))
  | andi (imm : BitVec 12) (rs1 rd : BitVec 5) : SequentialInstruction (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ANDI))
  | slli (amount : BitVec 6) (rs1 rd : BitVec 5) : SequentialInstruction (.SHIFTIOP (amount, .Regidx rs1, .Regidx rd, .SLLI))
  | srli (amount : BitVec 6) (rs1 rd : BitVec 5) : SequentialInstruction (.SHIFTIOP (amount, .Regidx rs1, .Regidx rd, .SRLI))
  | srai (amount : BitVec 6) (rs1 rd : BitVec 5) : SequentialInstruction (.SHIFTIOP (amount, .Regidx rs1, .Regidx rd, .SRAI))
  | rev8 (rs1 rd : BitVec 5) : SequentialInstruction (.REV8 (.Regidx rs1, .Regidx rd))
  | triadd (rs2 rs1 rd : BitVec 5) : SequentialInstruction (.ZIMOP_MOP_RR (4, .Regidx rs2, .Regidx rs1, .Regidx rd))
  | xorrot (mop rs1 rd : BitVec 5) : SequentialInstruction (.ZIMOP_MOP_R (mop, .Regidx rs1, .Regidx rd))

/-- Straight-path arithmetic, LW/SW, bitwise/shifts, REV8 and project MOPs. -/
def SequentialProgram (program : List UnifiedReduced.ProgramEntry) : Prop :=
  ∀ entry ∈ program, SequentialInstruction entry.instruction

/-- Sequential forms plus the four original comparisons, using RV32 PC addition. -/
inductive WrappedSequentialInstruction : SailRV32.instruction → Prop where
  | sequential {instruction} (supported : SequentialInstruction instruction) : WrappedSequentialInstruction instruction
  | slt (rs2 rs1 rd : BitVec 5) : WrappedSequentialInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLT))
  | sltu (rs2 rs1 rd : BitVec 5) : WrappedSequentialInstruction (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU))
  | slti (imm : BitVec 12) (rs1 rd : BitVec 5) : WrappedSequentialInstruction (.ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTI))
  | sltiu (imm : BitVec 12) (rs1 rd : BitVec 5) : WrappedSequentialInstruction (.ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU))

/-- Public instruction forms and code alignment for the wraparound PC profile. -/
structure WrappedSequentialProgram (program : List UnifiedReduced.ProgramEntry) : Prop where
  /-- Original decoded instructions; supported payload checks remain in public decoding. -/
  entries : ∀ entry ∈ program, WrappedSequentialInstruction entry.instruction
  /-- Alignment keeps comparison PC cleanup equal to the RV32 successor. -/
  aligned : ∀ entry ∈ program, entry.pc.toNat % 4 = 0

/-- Public registries identify the literal through native PC/clock matching. -/
inductive PreparationProgram [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat)
    (register : BitVec 5) (literal : ControlLiteral) : Prop where
  | uniform (entries : ∀ entry ∈ program, entry.instruction = literal.instruction register)
  | straight (entries : LiteralProgram program)
      (atCut : ∀ entry ∈ program,
        entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value =
          data.machine.initial.word.value + (cut - 4) →
        entry.instruction = literal.instruction register)
  | arithmetic (entries : ArithmeticProgram program)
      (atCut : ∀ entry ∈ program,
        entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value =
          data.machine.initial.word.value + (cut - 4) →
        entry.instruction = literal.instruction register)

  | sequential (entries : SequentialProgram program)
      (atCut : ∀ entry ∈ program,
        entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value =
          data.machine.initial.word.value + (cut - 4) →
        entry.instruction = literal.instruction register)

  | wrappedSequential (minimum : FieldCapacity.NativeRomCapacity p) (state : State)
      (setup : data.machine.rom = Setup.table state) (entries : WrappedSequentialProgram program)
      (atCut : ∀ entry ∈ program,
        entry.pc = data.machine.initial.word.toBitVec +
          BitVec.ofNat 32 (cut - 4 - (timeOfPair data.machine.initial.timestamp).value) →
        entry.instruction = literal.instruction register)

/-- Public preparation registry and its final cycle. Native matching identifies
    the final preparation row; no row selector, control read or write is supplied. -/
structure ControlPreparation [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) (cut : Nat) (register : BitVec 5) (literal : ControlLiteral) : Prop where
  /-- The public program profile binds the literal at the derived preparation address. -/
  program : PreparationProgram data program cut register literal
  /-- Workers may precede preparation, but none writes in its final cycle. -/
  prefixScope : data.workers.windowRows (cut - 4) cut = []
  /-- At least one complete preparation cycle follows the public initial clock. -/
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  /-- The cut lies within the accepted native machine path. -/
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- The actual control token retains the final preparation write's timestamp. -/
def PreparedControl (tokens : List (MemoryToken p)) (state : State) (cut : Nat)
    (register : BitVec 5) (literal : ControlLiteral) : Prop :=
  (Cell.register register).read state = .ok literal.value state ∧
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧ token.word.toBitVec = literal.value

end Airbender.UnifiedReduced.Caller
