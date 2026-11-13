module
public import Human.Helpers.UnifiedReduced.RVWindows
public import Human.Helpers.UnifiedReduced.ControlPreparation

@[expose] public section

/-! Public control literals and instruction registries stated over
    `RV.Instr`, the RV program table's instruction being `RV.decode entry.bits`. The literal kinds (`ControlLiteral`)
    are reused. -/

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- The `RV.Instr` writing a public constant: ADDI from x0 (`RV.decode` sign-extends the immediate) or LUI. -/
def ControlLiteral.rvInstruction (literal : ControlLiteral) (register : BitVec 5) : RV.Instr :=
  match literal with
  | .addi immediate => .opImm .add register 0 (immediate.signExtend 32)
  | .lui immediate => .lui register (immediate ++ (0 : BitVec 12))

/-- The constant written: the sign-extended I-immediate or the U-immediate, as `RV.decode` builds them. -/
def ControlLiteral.rvValue : ControlLiteral → BitVec 32
  | .addi immediate => immediate.signExtend 32
  | .lui immediate => immediate ++ (0 : BitVec 12)

/-- Every entry decodes to a public constant write to a nonzero register. -/
def RVLiteralProgram (program : List UnifiedReduced.RVProgramEntry) : Prop :=
  ∀ entry ∈ program, ∃ (register : BitVec 5) (literal : ControlLiteral),
    register ≠ (0 : BitVec 5) ∧ RV.decode entry.bits = some (literal.rvInstruction register)

/-- ADD/SUB/ADDI/LUI/AUIPC, operands and results unrestricted. -/
inductive RVArithmeticInstruction : RV.Instr → Prop where
  | add (rd rs1 rs2 : BitVec 5) : RVArithmeticInstruction (.op .add rd rs1 rs2)
  | sub (rd rs1 rs2 : BitVec 5) : RVArithmeticInstruction (.op .sub rd rs1 rs2)
  | addi (rd rs1 : BitVec 5) (imm : BitVec 32) : RVArithmeticInstruction (.opImm .add rd rs1 imm)
  | lui (rd : BitVec 5) (imm : BitVec 32) : RVArithmeticInstruction (.lui rd imm)
  | auipc (rd : BitVec 5) (imm : BitVec 32) : RVArithmeticInstruction (.auipc rd imm)

/-- Every entry decodes to an arithmetic instruction. -/
def RVArithmeticProgram (program : List UnifiedReduced.RVProgramEntry) : Prop :=
  ∀ entry ∈ program, ∀ instruction, RV.decode entry.bits = some instruction → RVArithmeticInstruction instruction

/-- Instruction forms using the native PC-increment path. -/
inductive RVSequentialInstruction : RV.Instr → Prop where
  | arithmetic {instruction} (supported : RVArithmeticInstruction instruction) : RVSequentialInstruction instruction
  | lw (rd rs1 : BitVec 5) (imm : BitVec 32) : RVSequentialInstruction (.load 4 true rd rs1 imm)
  | sw (rs2 rs1 : BitVec 5) (imm : BitVec 32) : RVSequentialInstruction (.store 4 rs2 rs1 imm)
  | xor (rd rs1 rs2 : BitVec 5) : RVSequentialInstruction (.op .xor rd rs1 rs2)
  | or (rd rs1 rs2 : BitVec 5) : RVSequentialInstruction (.op .or rd rs1 rs2)
  | and (rd rs1 rs2 : BitVec 5) : RVSequentialInstruction (.op .and rd rs1 rs2)
  | sll (rd rs1 rs2 : BitVec 5) : RVSequentialInstruction (.op .sll rd rs1 rs2)
  | srl (rd rs1 rs2 : BitVec 5) : RVSequentialInstruction (.op .srl rd rs1 rs2)
  | sra (rd rs1 rs2 : BitVec 5) : RVSequentialInstruction (.op .sra rd rs1 rs2)
  | xori (rd rs1 : BitVec 5) (imm : BitVec 32) : RVSequentialInstruction (.opImm .xor rd rs1 imm)
  | ori (rd rs1 : BitVec 5) (imm : BitVec 32) : RVSequentialInstruction (.opImm .or rd rs1 imm)
  | andi (rd rs1 : BitVec 5) (imm : BitVec 32) : RVSequentialInstruction (.opImm .and rd rs1 imm)
  | slli (rd rs1 : BitVec 5) (amount : BitVec 32) : RVSequentialInstruction (.opImm .sll rd rs1 amount)
  | srli (rd rs1 : BitVec 5) (amount : BitVec 32) : RVSequentialInstruction (.opImm .srl rd rs1 amount)
  | srai (rd rs1 : BitVec 5) (amount : BitVec 32) : RVSequentialInstruction (.opImm .sra rd rs1 amount)
  | rev8 (rd rs1 : BitVec 5) : RVSequentialInstruction (.rev8 rd rs1)
  | triadd (rd rs1 rs2 : BitVec 5) : RVSequentialInstruction (.mop .triAdd rd rs1 rs2)
  | xorrot (n rd rs1 : BitVec 5) : RVSequentialInstruction (.xorRot n rd rs1)

/-- Every entry decodes to a sequential instruction. -/
def RVSequentialProgram (program : List UnifiedReduced.RVProgramEntry) : Prop :=
  ∀ entry ∈ program, ∀ instruction, RV.decode entry.bits = some instruction → RVSequentialInstruction instruction

/-- Uniform literals or a public registry whose entry at the final preparation
    address decodes to the literal. -/
inductive RVPreparationProgram [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) (cut : Nat)
    (register : BitVec 5) (literal : ControlLiteral) : Prop where
  | uniform (entries : ∀ entry ∈ program, RV.decode entry.bits = some (literal.rvInstruction register))
  | straight (entries : RVLiteralProgram program)
      (atCut : ∀ entry ∈ program,
        entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value =
          data.machine.initial.word.value + (cut - 4) →
        RV.decode entry.bits = some (literal.rvInstruction register))
  | arithmetic (entries : RVArithmeticProgram program)
      (atCut : ∀ entry ∈ program,
        entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value =
          data.machine.initial.word.value + (cut - 4) →
        RV.decode entry.bits = some (literal.rvInstruction register))
  | sequential (entries : RVSequentialProgram program)
      (atCut : ∀ entry ∈ program,
        entry.pc.toNat + (timeOfPair data.machine.initial.timestamp).value =
          data.machine.initial.word.value + (cut - 4) →
        RV.decode entry.bits = some (literal.rvInstruction register))

/-- Public preparation registry and its final cycle. -/
structure RVControlPreparation [Fact p.Prime] (data : RVRequestTrace p)
    (program : List UnifiedReduced.RVProgramEntry) (cut : Nat) (register : BitVec 5) (literal : ControlLiteral) :
    Prop where
  program : RVPreparationProgram data program cut register literal
  prefixScope : data.workers.windowRows (cut - 4) cut = []
  afterInitial : (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut
  beforeTerminal : cut ≤ (timeOfPair data.machine.terminal.timestamp).value

/-- The control register reads the literal in the RV state, and the actual control
    token retains the final preparation write's timestamp. -/
def RVPreparedControl (tokens : List (MemoryToken p)) (state : RV.State) (cut : Nat)
    (register : BitVec 5) (literal : ControlLiteral) : Prop :=
  (Cell.register register).readRV state = some literal.rvValue ∧
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧
      (timeOfPair token.time).value = cut - 2 ∧ token.word.toBitVec = literal.rvValue

end Airbender.UnifiedReduced.Caller
