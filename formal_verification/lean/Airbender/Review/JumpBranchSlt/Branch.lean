import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Review.Sail
import Airbender.Review.Properties

namespace Airbender.JumpBranchSlt.Branch
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

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

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  SailRV32.Functions.execute_BTYPE input.encodedOffset input.rs2 input.rs1 input.opcode

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) Sail.zeroRegister output

def funct3 (opcode : SailRV32.bop) : Nat :=
  match opcode with
  | .BEQ => 0 | .BNE => 1 | .BLT => 4 | .BGE => 5 | .BLTU => 6 | .BGEU => 7

/-- Canonical observables and source/offset encodings in the imported assignment. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  operands : w 22 = (input.left.lo : ZMod p) ∧ w 23 = (input.left.hi : ZMod p) ∧
    w 26 = (input.right.lo : ZMod p) ∧ w 27 = (input.right.hi : ZMod p)
  pcOffset : input.pc.lo = (w 0).val ∧ input.pc.hi = (w 1).val ∧
    w 8 = (input.offset.lo : ZMod p) ∧ w 9 = (input.offset.hi : ZMod p) ∧
    output.pc.lo = (w 16).val ∧ output.pc.hi = (w 17).val
  destination : output.destination.lo = (w 30).val ∧ output.destination.hi = (w 31).val
  rs1Index : match input.rs1 with | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w 6 = (bits.toNat : ZMod p)

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Decoder identity, operand preprocessing and native state initialization remain
    interfaces. The imported equations determine the branch outcome and final PC. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  selected : w 14 = 1
  otherSelectors : w 11 = 0 ∧ w 12 = 0 ∧ w 13 = 0
  conditionTag : w 10 = (funct3 input.opcode : ZMod p)
  discardedDestination : w 15 = 1
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  offsetBound : input.offset.Bounded
  initialPCLoBound : input.pc.lo < limbBase
  pcAligned : input.pc.lo % 4 = 0
  offsetEven : input.offset.lo % 2 = 0
  finalPCHiBound : output.pc.hi < limbBase
  signExtension : input.offset.toBitVec = SailRV32.Functions.sign_extend (m := 32) input.encodedOffset
  leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.left.toBitVec input.before
  rightRead : run (SailRV32.Functions.rX_bits input.rs2) input.before =
    .ok input.right.toBitVec input.before
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before
  misaRead : ∃ value, run (SailRV32.readReg .misa) input.before = .ok value input.before

end Airbender.JumpBranchSlt.Branch
