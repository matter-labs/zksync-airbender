import Airbender.Review.UnifiedReduced.Decoder
import Airbender.Review.UnifiedReduced.Setup
import Airbender.Review.ShiftBinop.Model

namespace Airbender.UnifiedReduced.Binary
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace

abbrev Input := ShiftBinop.Input

/-- Canonical words observed in the imported unified register ports. All numeric
    placement IDs stay here; the model below uses named observations. -/
def leftWord {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 36).val, (w 37).val⟩
def rightWord {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 42).val, (w 43).val⟩
def initialPC {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 0).val, (w 1).val⟩
def destination {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 50).val, (w 51).val⟩
def finalPC {p : Nat} (w : Nat → ZMod p) : Word := ⟨(w 30).val, (w 31).val⟩

/-- Bind the observable Sail words to native port/PC values. This identifies
    inputs and outputs; it imposes no ranges, lookup answers or ISA result. -/
structure WordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  left : input.left = (leftWord w).toBitVec
  right : input.right = (rightWord w).toBitVec
  pc : input.pc = initialPC w
  result : output.destination = destination w
  nextPC : output.pc = finalPC w

/-- The original Sail constructors covered by this slice: register XOR/OR/AND.
    Unsupported operation/immediate combinations have no represented instruction. -/
def instruction (input : Input) : Option SailRV32.instruction :=
  match input.operation, input.immediate with
  | .xor, false => some (.RTYPE (input.rs2, input.rs1, input.rd, .XOR))
  | .or, false => some (.RTYPE (input.rs2, input.rs1, input.rd, .OR))
  | .and, false => some (.RTYPE (input.rs2, input.rs1, input.rd, .AND))
  | _, _ => none

/-- Locate this row in initialized unified history and the actual public program.
    Earlier writes supply the pre-state. Query equality binds the fetched original
    instruction; history proves its source reads, rather than assuming them. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  state : RowPosition trace initial cells ⟨.machine, w⟩ input.before
  instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
    instruction input = some entry.instruction

/-- Imported constraints and shared logical state/memory matching plus decoder
    membership. Other admitted unified operations may share the history. -/
def circuitModel {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Public initialization/program/clocks and the modeled pooled setup. Shared
    history and original decoding derive every operand/PC range, read, selector
    and byte interpretation. There are no per-row bounds or result premises. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (_input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop where
  initialization : NativeInputs decoderFields trace initial cells program
  setup : trace.rom = Setup.table initial

end Airbender.UnifiedReduced.Binary
