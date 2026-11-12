module
public import Human.Circuits.AddSub.RowInput
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
public import Human.Helpers.Context.RVRowModel
public import Human.Helpers.Decoder.RVPooledProgram
public import Human.ISA.RV32
public import Human.Helpers.Core.CircuitOutput

@[expose] public section

/-! RV32 vocabulary for the ADD/SUB/ADDI/LUI/AUIPC circuit: the input's instruction fields are RV registers and
    immediates, its pre-state is an `RV.State`, and its instruction is `RV.decode` of the public program entry.
    `Circuit.Output` (destination word and PC) is defined in `Helpers/Core/CircuitOutput.lean`. -/

namespace Airbender.AddSub
open Arithmetic Reference.RiscV Trace

/-- The circuit's input in RV32 terms; `row` is the decoder-preprocessed operands. -/
structure RVInput where
  /-- The circuit opcode and operand words. -/
  row : RowInput
  /-- The first source register index. -/
  rs1 : RV.Reg
  /-- The second source register index. -/
  rs2 : RV.Reg
  /-- The destination register index. -/
  rd : RV.Reg
  /-- Original 12-bit encoding; for ADDI, `row.immediate` is its 32-bit sign extension. -/
  encodedImmediate : BitVec 12
  /-- Original U-type encoding; the instruction appends twelve zero bits. -/
  encodedUpperImmediate : BitVec 20
  /-- The row's pre-state. -/
  before : RV.State

/-- The RV32 instruction the row executes, in our spec's vocabulary (`RV.decode` of its encoding). -/
def rvInstruction (input : RVInput) : RV.Instr :=
  match input.row.opcode with
  | .add => .op .add input.rd input.rs1 input.rs2
  | .addi => .opImm .add input.rd input.rs1 (input.encodedImmediate.signExtend 32)
  | .sub => .op .sub input.rd input.rs1 input.rs2
  | .lui => .lui input.rd (input.encodedUpperImmediate ++ 0#12)
  | .auipc => .auipc input.rd (input.encodedUpperImmediate ++ 0#12)

/-- Word mapping for the RV input: the imported variable IDs. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Bind the low limb of the left operand to its witness column. -/
  leftLo : input.row.left.lo = (w 25).val
  /-- Bind the high limb of the left operand to its witness column. -/
  leftHi : input.row.left.hi = (w 26).val
  /-- Bind the low limb of the right operand to its witness column. -/
  rightLo : input.row.right.lo = (w 29).val
  /-- Bind the high limb of the right operand to its witness column. -/
  rightHi : input.row.right.hi = (w 30).val
  /-- Bind the low limb of the decoded immediate to its witness column. -/
  immediateLo : input.row.immediate.lo = (w 8).val
  /-- Bind the high limb of the decoded immediate to its witness column. -/
  immediateHi : input.row.immediate.hi = (w 9).val
  /-- Bind the low limb of the starting PC to its witness column. -/
  pcLo : input.row.pc.lo = (w 0).val
  /-- Bind the high limb of the starting PC to its witness column. -/
  pcHi : input.row.pc.hi = (w 1).val
  /-- Bind the destination register index to its witness column. -/
  destinationIndex : w 7 = (input.rd.toNat : ZMod p)
  /-- Bind the low limb of the row result to its witness column. -/
  outputLo : output.destination.lo = (w 33).val
  /-- Bind the high limb of the row result to its witness column. -/
  outputHi : output.destination.hi = (w 34).val
  /-- Bind the low limb of the final PC to its witness column. -/
  finalPCLo : output.pc.lo = (w 19).val
  /-- Bind the high limb of the final PC to its witness column. -/
  finalPCHi : output.pc.hi = (w 20).val

/-- Assumptions of the RV statements: public initialization and modeled tables. -/
structure RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop
    extends RVPooledHistoryInputs trace initial cells program where
  /-- Every register belongs to the tracked cell domain. -/
  registersInitialized : ∀ index, Cell.register index ∈ cells

/-- A row of this family in an accepted, decoded trace, with its words, pre-state, and public program entry. -/
def rvModel (trace : PooledTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (program : List RVPooledProgramEntry) :=
  Trace.rvRowModel (family := .addSub) (before := RVInput.before) (instruction := rvInstruction)
    (words := RVWordMapping) trace initial cells program

/-- One step sets the destination register and the PC to the row's results. It changes no other visible state; x0's stored value is not visible. -/
def rvSpec (input : RVInput) (output : Circuit.Output) : Prop :=
  ∃ s', RV.step input.before = some s' ∧
    RV.Same s' ((input.before.setReg input.rd output.destination.toBitVec).setPC output.pc.toBitVec)

end Airbender.AddSub
