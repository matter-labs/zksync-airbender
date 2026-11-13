module
public import Human.Circuits.MulDiv.Artifact
public import Human.Circuits.MulDiv.Operation
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Context.RVRowModel
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.ISA.RV32
public import Human.Helpers.Core.CircuitOutput

@[expose] public section

/-! RV32 vocabulary for the MUL/MULHU/DIVU/REMU circuit (RV registers, an `RV.State` pre-state
    and the instruction `RV.decode` of the public program entry). `Circuit.Output` is the destination word and PC. -/

namespace Airbender.MulDiv
open Arithmetic Trace

/-- The circuit's input in RV32 terms: operation, operand words, start PC, register indices (they may alias; the
    divisor may be zero) and the row's pre-state. -/
structure RVInput where
  /-- The selected arithmetic or bit operation. -/
  operation : Operation
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
  /-- The row's pre-state. -/
  before : RV.State

/-- The RV32 instruction the row executes, in our spec's vocabulary (`RV.decode` of its encoding). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  match input.operation with
  | .mul => .op .mul input.rd input.rs1 input.rs2
  | .mulhu => .op .mulhu input.rd input.rs1 input.rs2
  | .divu => .op .divu input.rd input.rs1 input.rs2
  | .remu => .op .remu input.rd input.rs1 input.rs2

/-- Word mapping for the RV input: the imported variable IDs. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Bind the low limb of the left operand to its witness column. -/
  leftLo : input.left.lo = (w 20).val
  /-- Bind the high limb of the left operand to its witness column. -/
  leftHi : input.left.hi = (w 21).val
  /-- Bind the low limb of the right operand to its witness column. -/
  rightLo : input.right.lo = (w 24).val
  /-- Bind the high limb of the right operand to its witness column. -/
  rightHi : input.right.hi = (w 25).val
  /-- Bind the first source register index to its witness column. -/
  rs1Index : w 5 = (input.rs1.toNat : ZMod p)
  /-- Bind the second source register index to its witness column. -/
  rs2Index : w 6 = (input.rs2.toNat : ZMod p)
  /-- Bind the destination register index to its witness column. -/
  rdIndex : w 7 = (input.rd.toNat : ZMod p)
  /-- Bind the low limb of the starting PC to its witness column. -/
  pcLo : input.pc.lo = (w 0).val
  /-- Bind the high limb of the starting PC to its witness column. -/
  pcHi : input.pc.hi = (w 1).val
  /-- Bind the low limb of the row result to its witness column. -/
  outputLo : output.destination.lo = (w 28).val
  /-- Bind the high limb of the row result to its witness column. -/
  outputHi : output.destination.hi = (w 29).val
  /-- Bind the low limb of the final PC to its witness column. -/
  finalPCLo : output.pc.lo = (w 14).val
  /-- Bind the high limb of the final PC to its witness column. -/
  finalPCHi : output.pc.hi = (w 15).val

/-- Public initialization and ROM tables for this family. -/
abbrev RVAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  Trace.RVPooledHistoryInputs trace initial cells program

/-- A row of this family in an accepted, decoded trace, with its words, pre-state, and public program entry. -/
def rvModel (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) :=
  Trace.rvRowModel (family := .mulDiv) (before := RVInput.before) (instruction := rvInstruction)
    (words := RVWordMapping) trace initial cells program

/-- One step sets the destination register and the PC to the row's results. It changes no other visible state; x0's stored value is not visible. -/
def rvSpec (input : RVInput) (output : Circuit.Output) : Prop :=
  ∃ s', RV.step input.before = some s' ∧
    RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Airbender.MulDiv
