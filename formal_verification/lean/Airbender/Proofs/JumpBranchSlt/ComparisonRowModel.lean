import Airbender.Review.Circuits.JumpBranchSlt.Model

namespace Airbender.JumpBranchSlt.Comparison
open Airbender.Arithmetic Variables Airbender.Reference.RiscV Airbender.Reference.Sail

structure RowWordMapping {p : Nat} (input : Input) (output : Sail.Output)
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

def rowCircuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => RowWordMapping input output w

structure RowInterfaces {p : Nat} [Fact p.Prime] (input : Input)
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
