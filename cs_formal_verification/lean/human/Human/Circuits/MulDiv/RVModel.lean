module
public import Human.Circuits.MulDiv.Artifact
public import Human.Circuits.MulDiv.Operation
public import Human.Helpers.Context.RVInterfaces
public import Human.Helpers.Context.RVRowContext
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
  operation : Operation
  left : Word
  right : Word
  pc : Word
  rs1 : RV.Reg
  rs2 : RV.Reg
  rd : RV.Reg
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
  leftLo : input.left.lo = (w 20).val
  leftHi : input.left.hi = (w 21).val
  rightLo : input.right.lo = (w 24).val
  rightHi : input.right.hi = (w 25).val
  rs1Index : w 5 = (input.rs1.toNat : ZMod p)
  rs2Index : w 6 = (input.rs2.toNat : ZMod p)
  rdIndex : w 7 = (input.rd.toNat : ZMod p)
  pcLo : input.pc.lo = (w 0).val
  pcHi : input.pc.hi = (w 1).val
  outputLo : output.destination.lo = (w 28).val
  outputHi : output.destination.hi = (w 29).val
  finalPCLo : output.pc.lo = (w 14).val
  finalPCHi : output.pc.hi = (w 15).val

end Airbender.MulDiv
