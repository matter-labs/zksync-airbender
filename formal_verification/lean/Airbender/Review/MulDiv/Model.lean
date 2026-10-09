import Airbender.Review.MulDiv.Artifact
import Airbender.Review.Properties
import Airbender.Review.Sail
import Airbender.Review.Trace.PooledProgram
import Airbender.Review.Trace.RowContext
import Airbender.Review.SubwordTables

namespace Airbender.MulDiv
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail Trace

inductive Operation where
  | mul | mulhu | divu | remu

def Operation.selector : Operation → Fin 4
  | .mul => 0 | .mulhu => 1 | .divu => 2 | .remu => 3

/-- Original decoded operation and represented pre-state; registers may alias
    and divisors may be zero. -/
structure Input where
  operation : Operation
  left : Word
  right : Word
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  before : Sail.State

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  match input.operation with
  | .mul => SailRV32.Functions.execute_MUL input.rs2 input.rs1 input.rd
      ⟨.Low, .Signed, .Signed⟩
  | .mulhu => SailRV32.Functions.execute_MUL input.rs2 input.rs1 input.rd
      ⟨.High, .Unsigned, .Unsigned⟩
  | .divu => SailRV32.Functions.execute_DIV input.rs2 input.rs1 input.rd true
  | .remu => SailRV32.Functions.execute_REM input.rs2 input.rs1 input.rd true

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Canonical imported operands, register indices, result and both PCs. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : input.left.lo = (w 20).val
  leftHi : input.left.hi = (w 21).val
  rightLo : input.right.lo = (w 24).val
  rightHi : input.right.hi = (w 25).val
  rs1Index : match input.rs1 with | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w 6 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : input.pc.lo = (w 0).val
  pcHi : input.pc.hi = (w 1).val
  outputLo : output.destination.lo = (w 28).val
  outputHi : output.destination.hi = (w 29).val
  finalPCLo : output.pc.lo = (w 14).val
  finalPCHi : output.pc.hi = (w 15).val

/-- Interpret one unsigned mul/div assignment in the shared trace. Public
    starting state/program binding is supplied by `InterfaceAssumptions`; the
    imported constraints and logical matching are checked by `satisfies`. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry)
    (input : Input) (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  /-- Connect named operands, registers, result and PCs to the imported variables. -/
  words : WordMapping input output w
  /-- Obtain `input.before` from earlier native writes and this row's start PC.
      Actual reads and bounds are proved from initialized history. -/
  state : RowPosition trace initial cells ⟨.mulDiv, w⟩ input.before
  /-- Match the row's decoder query to the public instruction's original Sail constructor. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .mulDiv ∧
    (⟨.mulDiv, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    entry.instruction = match input.operation with
      | .mul => .MUL (input.rs2, input.rs1, input.rd, ⟨.Low, .Signed, .Signed⟩)
      | .mulhu => .MUL (input.rs2, input.rs1, input.rd, ⟨.High, .Unsigned, .Unsigned⟩)
      | .divu => .DIV (input.rs2, input.rs1, input.rd, true)
      | .remu => .REM (input.rs2, input.rs1, input.rd, true)

def circuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints ∧
    Accepted trace ∧ PooledDecoded trace program ∧ (⟨.mulDiv, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Public initialization and modeled tables for the shared history.
    Operand/PC bounds, reads and selector choices are derived internally;
    logical matching and membership retain their existing trust boundaries. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry)
    (_input : Input) (_output : Sail.Output) (_w : Nat → ZMod p) : Prop where
  initialization : NativeInputs pooledDecoderFields trace initial cells program
  wordTable : trace.rom.wordMemory = ROM.table cells trace.initialMemory
  subwordTable : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)

end Airbender.MulDiv
