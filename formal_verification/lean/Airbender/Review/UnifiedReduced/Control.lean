import Airbender.Review.UnifiedReduced.Decoder
import Airbender.Review.UnifiedReduced.Setup
import Airbender.Review.JumpBranchSlt.Branch

namespace Airbender.UnifiedReduced.Control
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace

/-- Native register, immediate, destination and PC observations. Numeric placement
    IDs stay here; the mappings below use these names. -/
def leftWord (w : Nat → ZMod p) : Word := ⟨(w 36).val, (w 37).val⟩
def rightWord (w : Nat → ZMod p) : Word := ⟨(w 42).val, (w 43).val⟩
def comparisonRight (w : Nat → ZMod p) : Word := ⟨(w 42 + w 8).val, (w 43 + w 9).val⟩
def offsetWord (w : Nat → ZMod p) : Word := ⟨(w 8).val, (w 9).val⟩
def initialPC (w : Nat → ZMod p) : Word := ⟨(w 0).val, (w 1).val⟩
def destination (w : Nat → ZMod p) : Word := ⟨(w 50).val, (w 51).val⟩
def finalPC (w : Nat → ZMod p) : Word := ⟨(w 30).val, (w 31).val⟩

/-- Public initialization/program/clocks, the modeled pooled setup and four-byte
    instruction alignment. History and decoding supply row ranges and reads;
    both final PC limbs are checked by native range queries. -/
structure Inputs [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) : Prop where
  initialization : NativeInputs decoderFields trace initial cells program
  setup : trace.rom = Setup.table initial
  codeAligned : ∀ entry ∈ program, entry.pc.toNat % 4 = 0

namespace Comparison
abbrev Input := JumpBranchSlt.Comparison.Input

/-- Identify the two operands, result and PCs. The right word combines the native
    rs2 and immediate columns; decoding makes one of them zero. -/
structure WordMapping (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  left : input.left = leftWord w
  right : input.right = comparisonRight w
  pc : input.pc = initialPC w
  result : output.destination = destination w
  nextPC : output.pc = finalPC w

/-- The original Sail comparison constructor, with its actual registers/immediate. -/
def instruction (input : Input) : SailRV32.instruction :=
  match input.opcode with
  | .slt => .RTYPE (input.rs2, input.rs1, input.rd, .SLT)
  | .slti => .ITYPE (input.encodedImmediate, input.rs1, input.rd, .SLTI)
  | .sltu => .RTYPE (input.rs2, input.rs1, input.rd, .SLTU)
  | .sltiu => .ITYPE (input.encodedImmediate, input.rs1, input.rd, .SLTIU)

/-- Locate the represented row in initialized history and the decoded public
    program. Neither source values nor the comparison answer are assumed. -/
structure TraceMapping [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  state : RowPosition trace initial cells ⟨.machine, w⟩ input.before
  instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧ entry.instruction = instruction input

abbrev InterfaceAssumptions [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (_input : Input) (_output : Output) (_w : Nat → ZMod p) := Inputs trace initial cells program

/-- Original imported constraints, decoder membership and shared logical matching,
    interpreted by the named words and actual public instruction above. -/
def circuitModel [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program
end Comparison

namespace Branch
abbrev Input := JumpBranchSlt.Branch.Input

/-- Identify the register operands, encoded offset, unused result and PCs.
    No branch decision or target is required by this mapping. -/
structure WordMapping (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  left : input.left = leftWord w
  right : input.right = rightWord w
  offset : input.offset = offsetWord w
  pc : input.pc = initialPC w
  result : output.destination = destination w
  nextPC : output.pc = finalPC w

def instruction (input : Input) : SailRV32.instruction :=
  .BTYPE (input.encodedOffset, input.rs2, input.rs1, input.opcode)

/-- Locate this branch in initialized history and the actual public program.
    Public decoding fixes its condition and offset; history proves its reads. -/
structure TraceMapping [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  state : RowPosition trace initial cells ⟨.machine, w⟩ input.before
  instruction : ∃ entry ∈ program, decoderQuery w = entry.query ∧ entry.instruction = instruction input

/-- Shared public inputs plus the readable Sail ISA configuration used by its
    branch-target alignment check. No operand or final-PC ranges are premises. -/
structure InterfaceAssumptions [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry)
    (_input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop extends Inputs trace initial cells program where
  isa : ∃ value, initial.regs.get? .misa = some value

/-- Original imported constraints, decoder membership and shared logical matching,
    interpreted by the branch's named word mapping. -/
def circuitModel [Fact p.Prime] (trace : UnifiedTrace p) (initial : State)
    (cells : List Cell) (program : List ProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ Decoded trace program ∧
    (⟨.machine, w⟩ : Row p UnifiedFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program
end Branch
end Airbender.UnifiedReduced.Control
