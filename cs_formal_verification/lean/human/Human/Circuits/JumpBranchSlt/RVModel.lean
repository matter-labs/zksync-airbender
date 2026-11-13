module
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Context.RVRowModel
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.Helpers.Core.CircuitOutput
public import Human.ISA.RV32

@[expose] public section

/-! RV32 vocabulary for the SLT/SLTI/SLTU/SLTIU, branch and JAL/JALR circuit: register fields are `RV.Reg`, the pre-state is an `RV.State`, and the instruction is `RV.decode` of
    the public program entry. `Comparison.Opcode` and `Jump.Instruction` (encodings only) and `Circuit.Output`
    (destination word and PC) are the circuit-side types. -/

namespace Airbender.JumpBranchSlt
open Arithmetic Trace

/-- Public conditions shared by comparisons, branches and jumps, in RV32 terms (no code-alignment premise: the
    program table's fetch guard, `rvProgramEntryWith`, aligns every PC). `terminalPC` stays: this circuit does not
    range-check the outgoing PC's high limb (column 17); a row's outgoing PC is canonical because it is the next
    row's incoming PC (a decoder-table PC) or, for the last row, the terminal PC. -/
structure RVTraceInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop
    extends RVPooledHistoryInputs trace initial cells program where
  /-- Both terminal-PC limbs are canonical 16-bit values; intermediate PCs are derived. -/
  terminalPC : trace.terminal.word.Bounded

end Airbender.JumpBranchSlt

namespace Airbender.JumpBranchSlt.Comparison
open Arithmetic Variables Trace

/-- The comparison's input in RV32 terms (`Input`); registers may alias. `right` is the second register word or the
    sign-extended immediate. -/
structure RVInput where
  /-- The selected comparison operation. -/
  opcode : Opcode
  /-- The left operand word. -/
  left : Word
  /-- The right operand word. -/
  right : Word
  /-- The row's starting PC. -/
  pc : Word
  /-- The first source register index. -/
  rs1 : RV.Reg
  /-- The second source register index. -/
  rs2 : RV.Reg
  /-- The destination register index. -/
  rd : RV.Reg
  /-- The original 12-bit immediate encoding. -/
  encodedImmediate : BitVec 12
  /-- The row's pre-state. -/
  before : RV.State

/-- The RV32 instruction the row executes, in our spec's vocabulary (`RV.decode` of its encoding). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  match input.opcode with
  | .slt => .op .slt input.rd input.rs1 input.rs2
  | .slti => .opImm .slt input.rd input.rs1 (input.encodedImmediate.signExtend 32)
  | .sltu => .op .sltu input.rd input.rs1 input.rs2
  | .sltiu => .opImm .sltu input.rd input.rs1 (input.encodedImmediate.signExtend 32)

/-- `WordMapping` for the RV input: the same imported variables. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Bind the low limb of the left operand to its witness column. -/
  leftLo : input.left.lo = (w rs1Lo).val
  /-- Bind the high limb of the left operand to its witness column. -/
  leftHi : input.left.hi = (w rs1Hi).val
  /-- Bind the low limb of the right operand to its witness column. -/
  rightLo : input.right.lo = (w rs2Lo + w immediateLo).val
  /-- Bind the high limb of the right operand to its witness column. -/
  rightHi : input.right.hi = (w rs2Hi + w immediateHi).val
  /-- Bind the first source register index to its witness column. -/
  rs1Index : w Variables.rs1Index = (input.rs1.toNat : ZMod p)
  /-- Bind the second source register index to its witness column. -/
  rs2Index : w Variables.rs2Index = (input.rs2.toNat : ZMod p)
  /-- Bind the destination register index to its witness column. -/
  rdIndex : w Variables.rdIndex = (input.rd.toNat : ZMod p)
  /-- Bind the low limb of the starting PC to its witness column. -/
  pcLo : input.pc.lo = (w initialPCLo).val
  /-- Bind the high limb of the starting PC to its witness column. -/
  pcHi : input.pc.hi = (w initialPCHi).val
  /-- Bind the low limb of the row result to its witness column. -/
  outputLo : output.destination.lo = (w destinationLo).val
  /-- Bind the high limb of the row result to its witness column. -/
  outputHi : output.destination.hi = (w destinationHi).val
  /-- Bind the low limb of the final PC to its witness column. -/
  finalPCLo : output.pc.lo = (w finalPCLo).val
  /-- Bind the high limb of the final PC to its witness column. -/
  finalPCHi : output.pc.hi = (w finalPCHi).val

/-- A row of this family in an accepted, decoded trace, with its words, pre-state, and public program entry. -/
def rvModel (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) :=
  Trace.rvRowModel (family := .jumpBranchSlt) (before := RVInput.before) (instruction := rvInstruction)
    (words := RVWordMapping) trace initial cells program

/-- One step sets the destination register and the PC to the row's results. It changes no other visible state; x0's stored value is not visible. -/
def rvSpec (input : RVInput) (output : Circuit.Output) : Prop :=
  ∃ s', RV.step input.before = some s' ∧
    RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Airbender.JumpBranchSlt.Comparison

namespace Airbender.JumpBranchSlt.Branch
open Arithmetic Variables Trace

/-- The branch's input in RV32 terms: `cond` is the RV branch condition. -/
structure RVInput where
  /-- The branch condition. -/
  cond : RV.Cond
  /-- The left operand word. -/
  left : Word
  /-- The right operand word. -/
  right : Word
  /-- The decoded branch or jump offset. -/
  offset : Word
  /-- The row's starting PC. -/
  pc : Word
  /-- The first source register index. -/
  rs1 : RV.Reg
  /-- The second source register index. -/
  rs2 : RV.Reg
  /-- The original branch-offset encoding. -/
  encodedOffset : BitVec 13
  /-- The row's pre-state. -/
  before : RV.State

/-- The RV32 instruction the row executes (`RV.decode` of its encoding). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  .branch input.cond input.rs1 input.rs2 (input.encodedOffset.signExtend 32)

/-- `WordMapping` for the RV input: the same imported variables. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Bind the low limb of the left operand to its witness column. -/
  leftLo : input.left.lo = (w rs1Lo).val
  /-- Bind the high limb of the left operand to its witness column. -/
  leftHi : input.left.hi = (w rs1Hi).val
  /-- Bind the low limb of the right operand to its witness column. -/
  rightLo : input.right.lo = (w rs2Lo).val
  /-- Bind the high limb of the right operand to its witness column. -/
  rightHi : input.right.hi = (w rs2Hi).val
  /-- Bind the low limb of the starting PC to its witness column. -/
  pcLo : input.pc.lo = (w initialPCLo).val
  /-- Bind the high limb of the starting PC to its witness column. -/
  pcHi : input.pc.hi = (w initialPCHi).val
  /-- Bind the low limb of the decoded offset to its witness column. -/
  offsetLo : input.offset.lo = (w immediateLo).val
  /-- Bind the high limb of the decoded offset to its witness column. -/
  offsetHi : input.offset.hi = (w immediateHi).val
  /-- Bind the low limb of the row result to its witness column. -/
  outputLo : output.destination.lo = (w destinationLo).val
  /-- Bind the high limb of the row result to its witness column. -/
  outputHi : output.destination.hi = (w destinationHi).val
  /-- Bind the low limb of the final PC to its witness column. -/
  finalPCLo : output.pc.lo = (w finalPCLo).val
  /-- Bind the high limb of the final PC to its witness column. -/
  finalPCHi : output.pc.hi = (w finalPCHi).val
  /-- Bind the first source register index to its witness column. -/
  rs1Index : w Variables.rs1Index = (input.rs1.toNat : ZMod p)
  /-- Bind the second source register index to its witness column. -/
  rs2Index : w Variables.rs2Index = (input.rs2.toNat : ZMod p)

/-- A row of this family in an accepted, decoded trace, with its words, pre-state, and public program entry. -/
def rvModel (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) :=
  Trace.rvRowModel (family := .jumpBranchSlt) (before := RVInput.before) (instruction := rvInstruction)
    (words := RVWordMapping) trace initial cells program

/-- One step sets the PC to the row's final PC. It changes no other visible state. -/
def rvSpec (input : RVInput) (output : Circuit.Output) : Prop :=
  ∃ s', RV.step input.before = some s' ∧ RV.Same s' (input.before.setPC output.pc.toBitVec)

end Airbender.JumpBranchSlt.Branch

namespace Airbender.JumpBranchSlt.Jump
open Arithmetic Variables Trace

/-- The jump's input in RV32 terms (`Input`). -/
structure RVInput where
  /-- The encoded jump form and offset. -/
  instruction : Instruction
  /-- The address-base operand word. -/
  source : Word
  /-- The decoded branch or jump offset. -/
  offset : Word
  /-- The row's starting PC. -/
  pc : Word
  /-- The first source register index. -/
  rs1 : RV.Reg
  /-- The destination register index. -/
  rd : RV.Reg
  /-- The row's pre-state. -/
  before : RV.State

/-- The target base: rs1's word for JALR, the PC for JAL (`Input.base`). -/
def RVInput.base (input : RVInput) : Word :=
  if input.instruction.indirect then input.source else input.pc

/-- The RV32 instruction the row executes (`RV.decode` of its encoding). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  match input.instruction with
  | .jal offset => .jal input.rd (offset.signExtend 32)
  | .jalr offset => .jalr input.rd input.rs1 (offset.signExtend 32)

/-- `WordMapping` for the RV input: the same imported variables. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Bind the low limb of the starting PC to its witness column. -/
  pcLo : input.pc.lo = (w initialPCLo).val
  /-- Bind the high limb of the starting PC to its witness column. -/
  pcHi : input.pc.hi = (w initialPCHi).val
  /-- Bind the low limb of the jump target base to its witness column. -/
  baseLo : input.base.lo = (w (if input.instruction.indirect then rs1Lo else initialPCLo)).val
  /-- Bind the high limb of the jump target base to its witness column. -/
  baseHi : input.base.hi = (w (if input.instruction.indirect then rs1Hi else initialPCHi)).val
  /-- Bind the low limb of the decoded offset to its witness column. -/
  offsetLo : input.offset.lo = (w immediateLo).val
  /-- Bind the high limb of the decoded offset to its witness column. -/
  offsetHi : input.offset.hi = (w immediateHi).val
  /-- Bind the low limb of the row result to its witness column. -/
  outputLo : output.destination.lo = (w destinationLo).val
  /-- Bind the high limb of the row result to its witness column. -/
  outputHi : output.destination.hi = (w destinationHi).val
  /-- Bind the low limb of the final PC to its witness column. -/
  finalPCLo : output.pc.lo = (w finalPCLo).val
  /-- Bind the high limb of the final PC to its witness column. -/
  finalPCHi : output.pc.hi = (w finalPCHi).val
  /-- Bind the first source register index to its witness column. -/
  rs1Index : input.instruction.indirect = true → w Variables.rs1Index = (input.rs1.toNat : ZMod p)
  /-- Bind the destination register index to its witness column. -/
  rdIndex : w Variables.rdIndex = (input.rd.toNat : ZMod p)

/-- A row of this family in an accepted, decoded trace, with its words, pre-state, and public program entry. -/
def rvModel (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) :=
  Trace.rvRowModel (family := .jumpBranchSlt) (before := RVInput.before) (instruction := rvInstruction)
    (words := RVWordMapping) trace initial cells program

/-- One step sets the destination register and the PC to the row's results. It changes no other visible state; x0's stored value is not visible. -/
def rvSpec (input : RVInput) (output : Circuit.Output) : Prop :=
  ∃ s', RV.step input.before = some s' ∧
    RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Airbender.JumpBranchSlt.Jump
