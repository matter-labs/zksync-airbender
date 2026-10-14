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

/-- Uniform literals, different literals, or ordinary arithmetic on a straight
    path. Native PC/clock matching locates the final public literal instruction. -/
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
