import Airbender.Review.Circuits.JumpBranchSlt.Branch

namespace Airbender.JumpBranchSlt.Branch
open Airbender.Arithmetic Variables Airbender.Reference.RiscV Airbender.Reference.Sail

structure RowWordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  operands : w rs1Lo = (input.left.lo : ZMod p) ∧ w rs1Hi = (input.left.hi : ZMod p) ∧
    w rs2Lo = (input.right.lo : ZMod p) ∧ w rs2Hi = (input.right.hi : ZMod p)
  pcOffset : input.pc.lo = (w initialPCLo).val ∧ input.pc.hi = (w initialPCHi).val ∧
    w immediateLo = (input.offset.lo : ZMod p) ∧ w immediateHi = (input.offset.hi : ZMod p) ∧
    output.pc.lo = (w finalPCLo).val ∧ output.pc.hi = (w finalPCHi).val
  destination : output.destination.lo = (w destinationLo).val ∧ output.destination.hi = (w destinationHi).val
  rs1Index : match input.rs1 with | .Regidx bits => w Variables.rs1Index = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w Variables.rs2Index = (bits.toNat : ZMod p)

def rowCircuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => RowWordMapping input output w

structure RowInterfaces {p : Nat} [Fact p.Prime] (input : Input)
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
