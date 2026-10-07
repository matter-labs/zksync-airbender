import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Review.Sail
import Airbender.Review.Properties

namespace Airbender.JumpBranchSlt.Comparison
open Airbender.Arithmetic
open Variables
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

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

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  match input.opcode with
  | .slt => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SLT
  | .slti => SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd .SLTI
  | .sltu => SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SLTU
  | .sltiu => SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd .SLTIU

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Operand encodings, native register indices and canonical PC/output decoding.
    This identifies observables without asserting instruction behavior. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : w rs1Lo = (input.left.lo : ZMod p)
  leftHi : w rs1Hi = (input.left.hi : ZMod p)
  rightLo : w rs2Lo + w immediateLo = (input.right.lo : ZMod p)
  rightHi : w rs2Hi + w immediateHi = (input.right.hi : ZMod p)
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

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Decoder and register/state interfaces, not consequences of the local circuit.
    Lookups bound the initial high PC limb and intermediate low PC. The final
    high limb is not range-checked here; its bound remains an explicit obligation. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  -- Decoder: comparison selection, immediate preprocessing and nonzero rd.
  active : w execute = 1
  selected : w comparisonSelector = 1
  otherSelectors : w jalSelector = 0 ∧ w jalrSelector = 0 ∧ w branchSelector = 0
  preprocessing : match input.opcode with
    | .slt | .sltu => w immediateLo = 0 ∧ w immediateHi = 0
    | .slti | .sltiu => input.rs2 = Sail.zeroRegister ∧ w rs2Lo = 0 ∧ w rs2Hi = 0
  funct3 : w conditionTag = match input.opcode with
    | .slt | .slti => 2
    | .sltu | .sltiu => 3
  nonzeroSelector : w discardedSelector = 0
  nonzeroDestination : input.rd ≠ Sail.zeroRegister
  -- Bounds/alignment not established by this artifact's lookups.
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  initialPCLoBound : input.pc.lo < limbBase
  pcAligned : input.pc.lo % 4 = 0
  finalPCHiBound : output.pc.hi < limbBase
  -- Encoded operands agree with the original Sail state.
  leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.left.toBitVec input.before
  rightRead : input.opcode = .slt ∨ input.opcode = .sltu →
    run (SailRV32.Functions.rX_bits input.rs2) input.before =
      .ok input.right.toBitVec input.before
  signExtension : input.opcode = .slti ∨ input.opcode = .sltiu →
    input.right.toBitVec = SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before

end Airbender.JumpBranchSlt.Comparison
