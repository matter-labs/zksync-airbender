import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Review.Sail
import Airbender.Review.Properties

namespace Airbender.JumpBranchSlt.Branch
open Airbender.Arithmetic
open Variables
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
  operands : w rs1Lo = (input.left.lo : ZMod p) ∧ w rs1Hi = (input.left.hi : ZMod p) ∧
    w rs2Lo = (input.right.lo : ZMod p) ∧ w rs2Hi = (input.right.hi : ZMod p)
  pcOffset : input.pc.lo = (w initialPCLo).val ∧ input.pc.hi = (w initialPCHi).val ∧
    w immediateLo = (input.offset.lo : ZMod p) ∧ w immediateHi = (input.offset.hi : ZMod p) ∧
    output.pc.lo = (w finalPCLo).val ∧ output.pc.hi = (w finalPCHi).val
  destination : output.destination.lo = (w destinationLo).val ∧ output.destination.hi = (w destinationHi).val
  rs1Index : match input.rs1 with | .Regidx bits => w Variables.rs1Index = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w Variables.rs2Index = (bits.toNat : ZMod p)

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Decoder identity, operand preprocessing and native state initialization remain
    interfaces. The imported equations determine the branch outcome and final PC. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  -- Decoder: select this instruction and discard its unused destination.
  active : w execute = 1
  selected : w branchSelector = 1
  otherSelectors : w jalSelector = 0 ∧ w jalrSelector = 0 ∧ w comparisonSelector = 0
  conditionTag : w Variables.conditionTag = (funct3 input.opcode : ZMod p)
  discardedDestination : w discardedSelector = 1
  -- Bounds/alignment not established by this artifact's lookups.
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  offsetBound : input.offset.Bounded
  initialPCLoBound : input.pc.lo < limbBase
  pcAligned : input.pc.lo % 4 = 0
  offsetEven : input.offset.lo % 2 = 0
  finalPCHiBound : output.pc.hi < limbBase
  -- Encoded offset and operands agree with the original Sail state.
  signExtension : input.offset.toBitVec = SailRV32.Functions.sign_extend (m := 32) input.encodedOffset
  leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.left.toBitVec input.before
  rightRead : run (SailRV32.Functions.rX_bits input.rs2) input.before =
    .ok input.right.toBitVec input.before
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before
  misaRead : ∃ value, run (SailRV32.readReg .misa) input.before = .ok value input.before

end Airbender.JumpBranchSlt.Branch
