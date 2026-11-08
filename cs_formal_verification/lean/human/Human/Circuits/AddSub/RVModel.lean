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
    `Circuit.Output` (destination word and PC, `Helpers/Core/CircuitOutput.lean`) is shared with the Sail statements. -/

namespace Airbender.AddSub
open Arithmetic Reference.RiscV Trace

/-- The circuit's input in RV32 terms; `row` is the decoder-preprocessed operands (as in `Reference.lean`). -/
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

/-- `WordMapping` (`Model.lean`) for the RV input: the same imported variable IDs. -/
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

/-- `TraceMapping` (`Model.lean`) in RV32 terms: the row's pre-state is the RV state at its clock position, and its
    decoder entry in the public program is `RV.decode` of the entry's encoding, equal to the input's instruction. -/
structure RVTraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry)
    (input : RVInput) (output : Circuit.Output) (w : Nat → ZMod p) : Prop where
  /-- Identify the input operands, destination register, result and both PCs with the variables. -/
  words : RVWordMapping input output w
  /-- Locate this row in clock order and obtain `input.before` from the starting state. -/
  state : RVRowPosition trace initial cells ⟨.addSub, w⟩ input.before
  /-- The row's family and decoder query match a public program entry whose encoding decodes to the row's
      instruction. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .addSub ∧ (⟨.addSub, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    RV.decode entry.bits = some (rvInstruction input)

/-- ADD/SUB's per-row model in RV32 terms (`circuitModel` with `RVTraceMapping`). -/
def rvCircuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) :
    Verification.CircuitModel RVInput Circuit.Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ RVPooledDecoded trace program ∧ (⟨.addSub, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := RVTraceMapping trace initial cells program

/-- The RV-typed assumptions: public initialization and modeled tables (`InterfaceAssumptions`, no `Configured`). -/
structure RVInterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : RV.State) (cells : List Cell) (program : List RVPooledProgramEntry) : Prop
    extends RVPooledHistoryInputs trace initial cells program where
  registersInitialized : ∀ index, Cell.register index ∈ cells

end Airbender.AddSub
