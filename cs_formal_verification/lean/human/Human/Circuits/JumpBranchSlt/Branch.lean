import Human.Circuits.JumpBranchSlt.Model
import Human.Helpers.Core.Sail
import Human.Helpers.Properties

namespace Airbender.JumpBranchSlt.Branch
open Airbender.Arithmetic
open Variables
open Airbender.Reference.RiscV
open Airbender.Reference.Sail Trace

/-- All six native Sail branch clauses share this input and verification contract. -/
structure Input where
  opcode : SailRV32.bop
  left : Word
  right : Word
  offset : Word
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  encodedOffset : BitVec 13
  before : Sail.State

/-- Original Sail constructor used by both public-program binding and execution. -/
def instruction (input : Input) : SailRV32.instruction :=
  .BTYPE (input.encodedOffset, input.rs2, input.rs1, input.opcode)

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  (Sail.registerClause (instruction input)).get (by rfl)

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) Sail.zeroRegister output

/-- Canonical operands, offset, PCs and unused destination in the imported row. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  leftLo : input.left.lo = (w rs1Lo).val
  leftHi : input.left.hi = (w rs1Hi).val
  rightLo : input.right.lo = (w rs2Lo).val
  rightHi : input.right.hi = (w rs2Hi).val
  pcLo : input.pc.lo = (w initialPCLo).val
  pcHi : input.pc.hi = (w initialPCHi).val
  offsetLo : input.offset.lo = (w immediateLo).val
  offsetHi : input.offset.hi = (w immediateHi).val
  outputLo : output.destination.lo = (w destinationLo).val
  outputHi : output.destination.hi = (w destinationHi).val
  finalPCLo : output.pc.lo = (w finalPCLo).val
  finalPCHi : output.pc.hi = (w finalPCHi).val
  rs1Index : match input.rs1 with | .Regidx bits => w Variables.rs1Index = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w Variables.rs2Index = (bits.toNat : ZMod p)

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
  /-- Identify a public entry with the same family and imported decoder query.
      Its original BTYPE constructor supplies the branch condition, register
      indices and encoded offset. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .jumpBranchSlt ∧
    (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    entry.instruction = instruction input

/-- Imported branch constraints together with shared trace acceptance and
    decoder membership. `TraceMapping` interprets the input/output; `soundness`
    proves that interpretation agrees with the original Sail execution. -/
def circuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ PooledDecoded trace program ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Public initialization/tables, aligned code and terminal-PC normalization,
    plus the public ISA register used by Sail's branch-target check. Trace
    helpers derive operand/offset bounds, actual reads and decoder preprocessing. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry)
    : Prop extends TraceInputs trace initial cells program where
  /-- Sail's branch-target check can read the public ISA configuration register. -/
  isa : ∃ value, initial.regs.get? .misa = some value

end Airbender.JumpBranchSlt.Branch
