import Airbender.Review.UnifiedReduced.Decoder
import Airbender.Review.Sail
import Airbender.Review.Properties
import Airbender.Review.Trace.RowContext

namespace Airbender.UnifiedReduced
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace

/-- Select the original Sail constructor from the arithmetic row view.
    This only names the instruction; its behavior is Sail's generated execution. -/
def arithmeticInstruction (input : Input) : SailRV32.instruction :=
  match input.row.opcode with
  | .add => .RTYPE (input.rs2, input.rs1, input.rd, .ADD)
  | .addi => .ITYPE (input.encodedImmediate, input.rs1, input.rd, .ADDI)
  | .sub => .RTYPE (input.rs2, input.rs1, input.rd, .SUB)
  | .lui => .UTYPE (input.encodedUpperImmediate, input.rd, .LUI)
  | .auipc => .UTYPE (input.encodedUpperImmediate, input.rd, .AUIPC)

/-- Canonical input/output limbs and destination index from the unified JSON.
    This identifies the declared words; it supplies no bounds or behavior. -/
structure WordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  leftLo : input.row.left.lo = (w 36).val
  leftHi : input.row.left.hi = (w 37).val
  rightLo : input.row.right.lo = (w 42).val
  rightHi : input.row.right.hi = (w 43).val
  immediateLo : input.row.immediate.lo = (w 8).val
  immediateHi : input.row.immediate.hi = (w 9).val
  pcLo : input.row.pc.lo = (w 0).val
  pcHi : input.row.pc.hi = (w 1).val
  destinationIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  outputLo : output.destination.lo = (w 50).val
  outputHi : output.destination.hi = (w 51).val
  finalPCLo : output.pc.lo = (w 30).val
  finalPCHi : output.pc.hi = (w 31).val

/-- Identify one standard arithmetic row and its Sail pre-state within `trace`.
    `words` names the imported variables. `state` applies earlier writes from
    public `initial`; initialized history separately proves the actual reads.
    `instruction` identifies the original Sail constructor in the public image,
    including original operands erased by x0 preprocessing. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  state : RowPosition trace initial cells ⟨.machine, w⟩ input.before
  instruction : ∃ entry ∈ program,
    decoderQuery w = entry.query ∧
    entry.instruction = arithmeticInstruction input

/-- The unified artifact and logical state/memory matching remain explicit.
    Only this row must be arithmetic; other admitted selectors may share its
    initialized history. Decoder membership is a logical lookup boundary. -/
def circuitModel {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Remaining arithmetic assumptions: public initialization, program and clocks,
    plus initialized registers for original sources erased by x0 preprocessing.
    Trace helpers derive operand/immediate/PC ranges, reads and native selectors.
    No setup-table behavior is needed by the arithmetic calculation. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop where
  initialization : NativeInputs decoderFields trace initial cells program
  registersInitialized : ∀ index,
    input.rs1 = .Regidx index ∨ input.rs2 = .Regidx index → Cell.register index ∈ cells

end Airbender.UnifiedReduced
