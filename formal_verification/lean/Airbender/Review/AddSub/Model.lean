import Airbender.Review.AddSub.Artifact
import Airbender.Review.Sail
import Airbender.Review.Properties
import Airbender.Review.Trace.PooledProgram
import Airbender.Review.SubwordTables
import Airbender.Review.Trace.RowContext

namespace Airbender.AddSub
open Arithmetic Reference.RiscV Reference.RiscV.Sail Trace

/-- Imported variable IDs and their canonical input/output interpretation. -/
structure WordMapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  leftLo : input.row.left.lo = (w 25).val
  leftHi : input.row.left.hi = (w 26).val
  rightLo : input.row.right.lo = (w 29).val
  rightHi : input.row.right.hi = (w 30).val
  immediateLo : input.row.immediate.lo = (w 8).val
  immediateHi : input.row.immediate.hi = (w 9).val
  pcLo : input.row.pc.lo = (w 0).val
  pcHi : input.row.pc.hi = (w 1).val
  destinationIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  outputLo : output.destination.lo = (w 33).val
  outputHi : output.destination.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 19).val
  finalPCHi : output.pc.hi = (w 20).val

/-- Canonical imported operands/output and the row's position in the shared
    history. Instruction tags map to original Sail constructors, not a new spec. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  words : WordMapping input output w
  state : RowPosition trace initial cells ⟨.addSub, w⟩ input.before
  instruction : ∃ entry ∈ program,
    entry.data.family = .addSub ∧ (⟨.addSub, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    entry.instruction = match input.row.opcode with
      | .add => .RTYPE (input.rs2, input.rs1, input.rd, .ADD)
      | .addi => .ITYPE (input.encodedImmediate, input.rs1, input.rd, .ADDI)
      | .sub => .RTYPE (input.rs2, input.rs1, input.rd, .SUB)
      | .lui => .UTYPE (input.encodedUpperImmediate, input.rd, .LUI)
      | .auipc => .UTYPE (input.encodedUpperImmediate, input.rd, .AUIPC)

/-- ADD/SUB's per-row model with shared logical memory/state matching and
    decoder lookup membership. `Accepted` checks the imported clock constraints
    of every participating family; the local artifact remains explicit here. -/
def circuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w =>
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints ∧
      Accepted trace ∧ PooledDecoded trace program ∧ (⟨.addSub, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Remaining ADD/SUB assumptions: public initialization and modeled tables.
    Source/immediate/PC bounds, successful register reads and decoder
    preprocessing are derived by Trace helpers. Matching/membership is logical;
    its cryptographic enforcement and table extraction remain outside this claim. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry)
    (_input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop where
  initialization : NativeInputs pooledDecoderFields trace initial cells program
  registersInitialized : ∀ index, Cell.register index ∈ cells
  wordTable : trace.rom.wordMemory = ROM.table cells trace.initialMemory
  subwordTable : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial)

end Airbender.AddSub
