import Airbender.Review.Circuits.JumpBranchSlt.Model
import Airbender.Review.Helpers.Core.Sail
import Airbender.Review.Helpers.Properties

namespace Airbender.JumpBranchSlt.Jump
open Airbender.Arithmetic
open Variables
open Airbender.Reference.RiscV
open Airbender.Reference.Sail Trace

inductive Instruction where
  | jal (offset : BitVec 21)
  | jalr (offset : BitVec 12)

def Instruction.indirect : Instruction → Bool
  | .jal _ => false | .jalr _ => true

/-- Native encodings and independently fixed architectural inputs. -/
structure Input where
  instruction : Instruction
  source : Word
  offset : Word
  pc : Word
  rs1 : SailRV32.regidx
  rd : SailRV32.regidx
  before : Sail.State

def Input.base (input : Input) : Word :=
  if input.instruction.indirect then input.source else input.pc

/-- Original Sail constructor used by both public-program binding and execution. -/
def instruction (input : Input) : SailRV32.instruction :=
  match input.instruction with
  | .jal imm => .JAL (imm, input.rd)
  | .jalr imm => .JALR (imm, input.rs1, input.rd)

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  (Sail.registerClause (instruction input)).get (by cases h_instruction : input.instruction <;> simp_all [instruction, Sail.registerClause])

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Canonical target operands, original register indices, link and PCs. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  pcLo : input.pc.lo = (w initialPCLo).val
  pcHi : input.pc.hi = (w initialPCHi).val
  baseLo : input.base.lo = (w (if input.instruction.indirect then rs1Lo else initialPCLo)).val
  baseHi : input.base.hi = (w (if input.instruction.indirect then rs1Hi else initialPCHi)).val
  offsetLo : input.offset.lo = (w immediateLo).val
  offsetHi : input.offset.hi = (w immediateHi).val
  outputLo : output.destination.lo = (w destinationLo).val
  outputHi : output.destination.hi = (w destinationHi).val
  finalPCLo : output.pc.lo = (w finalPCLo).val
  finalPCHi : output.pc.hi = (w finalPCHi).val
  rs1Index : input.instruction.indirect = true → match input.rs1 with
    | .Regidx bits => w Variables.rs1Index = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w Variables.rdIndex = (bits.toNat : ZMod p)

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
      Its original JAL/JALR constructor supplies the encoded offset, source
      register when used, and link register. -/
  instruction : ∃ entry ∈ program,
    entry.data.family = .jumpBranchSlt ∧
    (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily).decoderQuery = entry.query ∧
    entry.instruction = instruction input

/-- Imported jump constraints together with shared trace acceptance and decoder
    membership. `TraceMapping` interprets the input/output; `soundness` proves
    that interpretation agrees with the original Sail execution. -/
def circuitModel {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry) :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => Accepted trace ∧ PooledDecoded trace program ∧ (⟨.jumpBranchSlt, w⟩ : Row p PooledFamily) ∈ trace.rows
  represents := TraceMapping trace initial cells program

/-- Public initialization/tables, aligned code and terminal-PC normalization,
    plus Sail's ISA and JALR landing-pad configuration. Trace helpers derive
    target/offset bounds, actual reads and decoder preprocessing. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (trace : PooledTrace p)
    (initial : Sail.State) (cells : List Cell) (program : List PooledProgramEntry)
    (input : Input) (_output : Sail.Output) (_w : Nat → ZMod p)
    : Prop extends TraceInputs trace initial cells program where
  /-- Sail's target-alignment check can read the public ISA configuration register. -/
  isa : ∃ value, initial.regs.get? .misa = some value
  /-- Only JALR needs the Machine/MLPE-clear landing-pad configuration. -/
  landingPad : input.instruction.indirect = true →
    initial.regs.get? .cur_privilege = some .Machine ∧
      ∃ security, initial.regs.get? .mseccfg = some security ∧
        SailRV32.Functions._get_Seccfg_MLPE security = 0

end Airbender.JumpBranchSlt.Jump
