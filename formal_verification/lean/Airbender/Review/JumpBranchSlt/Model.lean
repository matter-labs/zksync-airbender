import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Review.Sail
import Airbender.Review.Properties
import Airbender.Review.Trace.PooledProgram
import Airbender.Review.Trace.RowContext
import Airbender.Review.Trace.Interfaces

namespace Airbender.JumpBranchSlt
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace

/-- Public conditions shared by comparisons, branches and jumps. `initial`
    supplies Sail state and program bytes; `cells` lists tracked registers/RAM;
    `program` is built by actual Sail decoding. Shared history derives per-row
    bounds and reads. Terminal-PC normalization remains an external condition
    until teardown supplies a checked range proof. -/
structure TraceInputs {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : State) (cells : List Cell) (program : List PooledProgramEntry) : Prop extends PooledHistoryInputs trace initial cells program where
  /-- Public instruction PCs are four-byte aligned; decoder membership transfers this to rows. -/
  codeAligned : ∀ entry ∈ program, entry.pc.toNat % 4 = 0
  /-- Both terminal-PC limbs are canonical 16-bit values; intermediate PCs are derived. -/
  terminalPC : trace.terminal.word.Bounded

end Airbender.JumpBranchSlt

namespace Airbender.JumpBranchSlt.Comparison
open Airbender.Arithmetic
open Variables
open Airbender.Reference.RiscV
open Airbender.Reference.Sail Trace

/-- Standard Sail clauses covered by this comparison slice. -/
inductive Opcode where
  | slt | slti | sltu | sltiu
  deriving Repr, DecidableEq

/-- Fixed architectural input; registers may alias. `right` is the second register
    word or the sign-extended immediate. Writes to x0 remain outside this slice. -/
structure Input where
  opcode : Opcode
  left : Word
  right : Word
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  encodedImmediate : BitVec 12
  before : Sail.State

/-- Original Sail constructor used by both public-program binding and execution. -/
def instruction (input : Input) : SailRV32.instruction :=
  match input.opcode with
  | .slt => .RTYPE (input.rs2, input.rs1, input.rd, .SLT)
  | .slti => .ITYPE (input.encodedImmediate, input.rs1, input.rd, .SLTI)
  | .sltu => .RTYPE (input.rs2, input.rs1, input.rd, .SLTU)
  | .sltiu => .ITYPE (input.encodedImmediate, input.rs1, input.rd, .SLTIU)

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  (Sail.registerClause (instruction input)).get (by cases h_opcode : input.opcode <;> simp_all [instruction, Sail.registerClause])

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Operand encodings, native register indices and canonical PC/output decoding.
    This identifies observables without asserting instruction behavior. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : input.left.lo = (w rs1Lo).val
  leftHi : input.left.hi = (w rs1Hi).val
  rightLo : input.right.lo = (w rs2Lo + w immediateLo).val
  rightHi : input.right.hi = (w rs2Hi + w immediateHi).val
  rs1Index : match input.rs1 with
    | .Regidx bits => w Variables.rs1Index = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with
    | .Regidx bits => w Variables.rs2Index = (bits.toNat : ZMod p)
  rdIndex : match input.rd with
    | .Regidx bits => w Variables.rdIndex = (bits.toNat : ZMod p)
  pcLo : input.pc.lo = (w initialPCLo).val
  pcHi : input.pc.hi = (w initialPCHi).val
  outputLo : output.destination.lo = (w destinationLo).val
  outputHi : output.destination.hi = (w destinationHi).val
  finalPCLo : output.pc.lo = (w finalPCLo).val
  finalPCHi : output.pc.hi = (w finalPCHi).val

/-- Interpret this row using the public initial state, tracked `cells` and
    public decoded `program`. The shared inputs bind initialization; satisfaction
    checks imported constraints and logical matching/membership. -/
structure TraceMapping {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry)
    (input : Input) (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  /-- Name the imported operand, register, destination and PC variables. -/
  words : WordMapping input output w
  /-- Build `input.before` from earlier native writes and this row's start PC;
      reads and bounds are proved from initialized history. -/
  state : RowPosition trace initial cells ⟨.jumpBranchSlt, w⟩ input.before
  /-- Identify a public program entry with the same family and imported decoder
      query. Its original Sail constructor supplies this input's opcode,
      register indices and encoded immediate. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .jumpBranchSlt ∧
    (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    entry.instruction = instruction input

/-- Imported comparison constraints together with shared trace acceptance and
    decoder membership. `TraceMapping` interprets the input/output; `soundness`
    proves that interpretation agrees with the original Sail execution. -/
def circuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints ∧
    Accepted trace ∧ PooledDecoded trace program ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Shared public initialization/tables, aligned code and canonical terminal PC.
    Operand bounds, reads and decoder contracts are proved internally. -/
abbrev InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) : Prop :=
  TraceInputs trace initial cells program

end Airbender.JumpBranchSlt.Comparison
