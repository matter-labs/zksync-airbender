import Airbender.Review.ShiftBinop.Artifact
import Airbender.Review.Properties
import Airbender.Review.Sail
import Airbender.Review.Trace.PooledProgram
import Airbender.Review.Trace.RowContext

namespace Airbender.ShiftBinop
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail Trace

/-- Native source words; binary immediates use `right` after Sail sign extension.
    Immediate shifts use the encoded payload. Source and destination may alias. -/
structure Input where
  operation : Operation
  immediate : Bool
  left : BitVec 32
  right : BitVec 32
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  encodedImmediate : BitVec 12
  before : Sail.State

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  match input.operation, input.immediate with
  | .rev8, _ => SailRV32.Functions.execute_REV8 input.rs1 input.rd
  | .xor, true => SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd .XORI
  | .or, true => SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd .ORI
  | .and, true => SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd .ANDI
  | .sll, true => SailRV32.Functions.execute_SHIFTIOP (input.encodedImmediate.extractLsb' 0 6) input.rs1 input.rd .SLLI
  | .srl, true => SailRV32.Functions.execute_SHIFTIOP (input.encodedImmediate.extractLsb' 0 6) input.rs1 input.rd .SRLI
  | .sra, true => SailRV32.Functions.execute_SHIFTIOP (input.encodedImmediate.extractLsb' 0 6) input.rs1 input.rd .SRAI
  | .xor, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .XOR
  | .or, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .OR
  | .and, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .AND
  | .sll, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SLL
  | .srl, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SRL
  | .sra, false => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SRA

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Binary queries combine rs2 bytes with the packed immediate/sign byte.
    Shift queries use rs2 truncation plus the immediate's low five bits; REV8 uses zero.
    These mappings identify operands; none prescribes the result. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
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
  rs1Index : match input.rs1 with | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w 6 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : input.pc.lo = (w 0).val
  pcHi : input.pc.hi = (w 1).val
  outputLo : output.destination.lo = (w 31).val
  outputHi : output.destination.hi = (w 32).val
  finalPCLo : output.pc.lo = (w 13).val
  finalPCHi : output.pc.hi = (w 14).val

/-- Interpret a shift/binop assignment in the shared trace. `initial` is the
    public starting Sail state; `cells` names the tracked registers/RAM; `program`
    is decoded from its public bytes by `InterfaceAssumptions.initialization`.
    This mapping interprets variables and the pre-state; it assumes no ISA result. -/
structure TraceMapping {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (trace : PooledTrace p) (initial : Sail.State) (cells : List Cell)
    (program : List PooledProgramEntry) (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  /-- Name the imported operand bytes, registers, result and PC variables. -/
  words : WordMapping input output w
  /-- Build `input.before` from earlier native writes and this row's start PC.
      Initialized history supplies actual reads and bounds in the proof. -/
  state : RowPosition trace initial cells ⟨.shiftBinop, w⟩ input.before
  /-- Bind the decoder query to a public instruction whose original Sail clause
      is `execution input`. This identifies the instruction, not its outcome. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .shiftBinop ∧
    (⟨.shiftBinop, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    instructionClause entry.instruction = some (execution input)

def circuitModel {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (trace : PooledTrace p) (initial : Sail.State) (cells : List Cell)
    (program : List PooledProgramEntry) :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints ∧
    Accepted trace ∧ PooledDecoded trace program ∧ (⟨.shiftBinop, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Public initialization for the shared history. Operand/PC bounds, actual
    reads, selectors and immediate preprocessing are derived internally.
    Modeled byte tables and logical matching retain their existing boundaries. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry)
    (_input : Input) (_output : Sail.Output) (_w : Nat → ZMod p) : Prop where
  initialization : NativeInputs pooledDecoderFields trace initial cells program

end Airbender.ShiftBinop
