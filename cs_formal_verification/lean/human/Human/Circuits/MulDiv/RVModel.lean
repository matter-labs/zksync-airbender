import Human.Circuits.MulDiv.Artifact
import Human.Circuits.MulDiv.Operation
import Human.Helpers.Context.RVInterfaces
import Human.Helpers.Context.RVRowContext
import Human.Helpers.Decoder.RVPooledProgram
import Human.ISA.RV32
import Human.Helpers.Core.CircuitOutput

/-! RV32 vocabulary for the MUL/MULHU/DIVU/REMU circuit (as `Model.lean`, with RV registers, an `RV.State` pre-state
    and the instruction `RV.decode` of the public program entry). `Circuit.Output` (destination word and PC) is shared
    with the Sail statements. -/

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

/-- `WordMapping` (`Model.lean`) for the RV input: the same imported variable IDs. -/
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

/-- `TraceMapping` (`Model.lean`) in RV32 terms: the row's pre-state is the RV state at its clock position, and its
    decoder entry in the public program is `RV.decode` of the entry's encoding, equal to the input's instruction. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Connect named operands, registers, result and PCs to the imported variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.mulDiv, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .mulDiv ∧ (⟨.mulDiv, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- MUL/DIV's per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Circuit.Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ RVPooledDecoded trace program ∧ (⟨.mulDiv, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- The RV-typed assumptions: public initialization and modeled tables (`InterfaceAssumptions`, no `Configured`). -/
abbrev RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  RVPooledHistoryInputs trace initial cells program

end Airbender.MulDiv
