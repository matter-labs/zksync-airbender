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

/-- Interpret one ADD/SUB assignment `w` as a Sail `input` and `output` within
    the shared `trace`. `initial` is the public starting Sail state; `cells`
    lists the tracked registers and RAM words. `program` holds decoded
    instruction entries, bound to public bytes by
    `InterfaceAssumptions.initialization`.

    `circuitModel` uses this as its `represents` relation. It checks the imported
    constraints and logical trace matching in `satisfies`; the `soundness`
    theorem proves that the resulting input/output agrees with Sail execution. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry)
    (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  /-- Identify the input operands, destination register, result and both PCs
      with the variables listed in `WordMapping`. -/
  words : WordMapping input output w
  /-- Locate this row in clock order. Apply all earlier register/RAM writes to
      `initial`, then set Sail's PC and nextPC to this row's start PC to obtain
      `input.before`. The soundness proof derives reads and bounds from the
      accepted, initialized history. -/
  state : RowPosition trace initial cells ⟨.addSub, w⟩ input.before
  /-- Connect the row to an instruction in the public program: its family and
      decoder query match the row, and its original Sail constructor matches
      the opcode, register indices and encoded immediate supplied by `input`. -/
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
