import Human.Circuits.ShiftBinop.Artifact
import Human.Helpers.Context.RVInterfaces
import Human.Helpers.Context.RVRowContext
import Human.Helpers.Decoder.RVPooledProgram
import Human.ISA.RV32
import Human.Helpers.Core.CircuitOutput

/-! RV32 vocabulary for the XOR/OR/AND, SLL/SRL/SRA (register and immediate forms) and REV8 circuit (as
    `Model.lean`, with RV registers, an `RV.State` pre-state and the instruction `RV.decode` of the public program
    entry). `Circuit.Output` (destination word and PC) is shared with the Sail statements. -/

namespace Airbender.ShiftBinop
open Arithmetic Trace

/-- The circuit's input in RV32 terms: operation and form, operand words (for binary immediates `right` is the
    sign-extended immediate), start PC, register indices (they may alias), the 12-bit encoded immediate and the row's
    pre-state. -/
structure RVInput where
  operation : Operation
  immediate : Bool
  left : BitVec 32
  right : BitVec 32
  pc : Word
  rs1 : RV.Reg
  rs2 : RV.Reg
  rd : RV.Reg
  encodedImmediate : BitVec 12
  before : RV.State

/-- The RV32 instruction the row executes, in our spec's vocabulary (`RV.decode` of its encoding): binary immediates
    are sign-extended, immediate shift amounts are the encoding's low five bits (the `rs2` field), zero-extended. -/
def rvInstruction (input : RVInput) : RV.Instr :=
  match input.operation, input.immediate with
  | .rev8, _ => .rev8 input.rd input.rs1
  | .xor, true => .opImm .xor input.rd input.rs1 (input.encodedImmediate.signExtend 32)
  | .or, true => .opImm .or input.rd input.rs1 (input.encodedImmediate.signExtend 32)
  | .and, true => .opImm .and input.rd input.rs1 (input.encodedImmediate.signExtend 32)
  | .sll, true => .opImm .sll input.rd input.rs1 ((input.encodedImmediate.extractLsb' 0 5).zeroExtend 32)
  | .srl, true => .opImm .srl input.rd input.rs1 ((input.encodedImmediate.extractLsb' 0 5).zeroExtend 32)
  | .sra, true => .opImm .sra input.rd input.rs1 ((input.encodedImmediate.extractLsb' 0 5).zeroExtend 32)
  | .xor, false => .op .xor input.rd input.rs1 input.rs2
  | .or, false => .op .or input.rd input.rs1 input.rs2
  | .and, false => .op .and input.rd input.rs1 input.rs2
  | .sll, false => .op .sll input.rd input.rs1 input.rs2
  | .srl, false => .op .srl input.rd input.rs1 input.rs2
  | .sra, false => .op .sra input.rd input.rs1 input.rs2

/-- `WordMapping` (`Model.lean`) for the RV input: the same imported variable IDs. These mappings identify operands;
    none prescribes the result. -/
structure RVWordMapping {p : Nat} (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  leftBytes : ∀ i : Fin 4,
    w (19 + i.val) = ((input.left.extractLsb' (8 * i.val) 8).toNat : ZMod p)
  binaryRightBytes : input.operation.isShift = false → ∀ i : Fin 4,
    w (25 + i.val) +
      (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35) =
      ((BitVec.extractLsb' (8 * i.val) 8
        input.right).toNat : ZMod p)
  shiftLowByte : input.operation.isShift = true →
    w 25 = ((BitVec.extractLsb' 0 8
      (if input.immediate || input.operation = .rev8 then 0 else input.right)).toNat : ZMod p)
  shiftImmediate : input.operation.isShift = true →
    w 8 = (if input.operation = .rev8 then 0 else if input.immediate then (input.encodedImmediate.extractLsb' 0 5).toNat else 0 : ZMod p)
  rs1Index : w 5 = (input.rs1.toNat : ZMod p)
  rs2Index : w 6 = (input.rs2.toNat : ZMod p)
  rdIndex : w 7 = (input.rd.toNat : ZMod p)
  pcLo : input.pc.lo = (w 0).val
  pcHi : input.pc.hi = (w 1).val
  outputLo : output.destination.lo = (w 31).val
  outputHi : output.destination.hi = (w 32).val
  finalPCLo : output.pc.lo = (w 13).val
  finalPCHi : output.pc.hi = (w 14).val

/-- `TraceMapping` (`Model.lean`) in RV32 terms: the row's pre-state is the RV state at its clock position, and its
    decoder entry in the public program is `RV.decode` of the entry's encoding, equal to the input's instruction. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Connect named operands, registers, result and PCs to the imported variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.shiftBinop, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .shiftBinop ∧ (⟨.shiftBinop, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- The shift/binop per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Circuit.Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ RVPooledDecoded trace program ∧
    (⟨.shiftBinop, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- The RV-typed assumptions: public initialization and modeled tables (`InterfaceAssumptions`, no `Configured`). -/
abbrev RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop :=
  RVPooledHistoryInputs trace initial cells program

end Airbender.ShiftBinop
