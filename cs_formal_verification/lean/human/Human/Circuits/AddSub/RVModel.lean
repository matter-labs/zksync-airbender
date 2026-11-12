module
public import Human.Circuits.AddSub.RowInput
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
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
  row : RowInput
  rs1 : RV.Reg
  rs2 : RV.Reg
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
  leftLo : input.row.left.lo = (w 25).val
  leftHi : input.row.left.hi = (w 26).val
  rightLo : input.row.right.lo = (w 29).val
  rightHi : input.row.right.hi = (w 30).val
  immediateLo : input.row.immediate.lo = (w 8).val
  immediateHi : input.row.immediate.hi = (w 9).val
  pcLo : input.row.pc.lo = (w 0).val
  pcHi : input.row.pc.hi = (w 1).val
  destinationIndex : w 7 = (input.rd.toNat : ZMod p)
  outputLo : output.destination.lo = (w 33).val
  outputHi : output.destination.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 19).val
  finalPCHi : output.pc.hi = (w 20).val

/-- Assumptions of the RV statements: public initialization and modeled tables. -/
structure RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop
    extends RVPooledHistoryInputs trace initial cells program where
  registersInitialized : ∀ index, Cell.register index ∈ cells

end Airbender.AddSub
