import Human.Circuits.UnifiedReduced.Binary

namespace Airbender.UnifiedReduced.Shift
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace

abbrev Input := Binary.Input
abbrev WordMapping := @Binary.WordMapping

/-- The original Sail constructors for the three register/immediate shifts
    and REV8. Decoder membership supplies the legal RV32 immediate payload. -/
def instruction (input : Input) : Option SailRV32.instruction :=
  match input.operation, input.immediate with
  | .sll, false => some (.RTYPE (input.rs2, input.rs1, input.rd, .SLL))
  | .srl, false => some (.RTYPE (input.rs2, input.rs1, input.rd, .SRL))
  | .sra, false => some (.RTYPE (input.rs2, input.rs1, input.rd, .SRA))
  | .sll, true => some (.SHIFTIOP (input.encodedImmediate.extractLsb' 0 6, input.rs1, input.rd, .SLLI))
  | .srl, true => some (.SHIFTIOP (input.encodedImmediate.extractLsb' 0 6, input.rs1, input.rd, .SRLI))
  | .sra, true => some (.SHIFTIOP (input.encodedImmediate.extractLsb' 0 6, input.rs1, input.rd, .SRAI))
  | .rev8, _ => some (.REV8 (input.rs1, input.rd))
  | _, _ => none

/-- Use the same named native words as unified binops. `state` locates this
    row after prior writes; `instruction` binds its query to actual public Sail
    decoding. No operand bound, expected read, shift amount or result is assumed. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  state : RowPosition trace initial cells ⟨.machine, w⟩ input.before
  instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧
    instruction input = some entry.instruction

/-- Imported constraints with initialized shared history and program membership.
    Other admitted unified branches may participate in the same history. -/
def circuitModel {p : Nat} [Fact p.Prime] (trace : UnifiedTrace p)
    (initial : State) (cells : List Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Reuse the public initialization, program/clocks and modeled pooled setup
    boundary. Shared history derives source/PC bounds and x0 reads; the decoder
    and truncation query derive the operation and its amount internally. -/
abbrev InterfaceAssumptions := @Binary.InterfaceAssumptions

end Airbender.UnifiedReduced.Shift
