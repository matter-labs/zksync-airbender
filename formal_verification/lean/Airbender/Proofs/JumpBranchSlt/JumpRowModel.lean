import Airbender.Review.JumpBranchSlt.Jump

namespace Airbender.JumpBranchSlt.Jump
open Airbender.Arithmetic Variables Airbender.Reference.RiscV Airbender.Reference.Sail

structure RowWordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  initialPC : input.pc.lo = (w initialPCLo).val ∧ input.pc.hi = (w initialPCHi).val
  targetWords : input.base.lo = (w (if input.instruction.indirect then rs1Lo else initialPCLo)).val ∧
    input.base.hi = (w (if input.instruction.indirect then rs1Hi else initialPCHi)).val ∧
    w immediateLo = (input.offset.lo : ZMod p) ∧ w immediateHi = (input.offset.hi : ZMod p) ∧
    output.pc.lo = (w finalPCLo).val ∧ output.pc.hi = (w finalPCHi).val
  destination : output.destination.lo = (w destinationLo).val ∧ output.destination.hi = (w destinationHi).val
  rs1Index : input.instruction.indirect = true → match input.rs1 with
    | .Regidx bits => w Variables.rs1Index = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w Variables.rdIndex = (bits.toNat : ZMod p)

def rowCircuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => RowWordMapping input output w

structure RowInterfaces {p : Nat} [Fact p.Prime] (input : Input)
    (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  -- Decoder: JAL/JALR selection and the x0 destination mask.
  active : w execute = 1
  selected : w jalSelector = (if input.instruction.indirect then 0 else 1) ∧
    w jalrSelector = (if input.instruction.indirect then 1 else 0)
  otherSelectors : w comparisonSelector = 0 ∧ w branchSelector = 0
  zeroDestination : w discardedSelector = 1 ↔ input.rd = Sail.zeroRegister
  -- Bounds/parity not established by this artifact's lookups.
  initialPCLoBound : input.pc.lo < limbBase
  baseLoBound : input.base.lo < limbBase
  sourceHiBound : input.instruction.indirect = true → input.base.hi < limbBase
  offsetBound : input.offset.Bounded
  directEven : input.instruction.indirect = false → input.base.lo % 2 = 0 ∧ input.offset.lo % 2 = 0
  finalPCHiBound : output.pc.hi < limbBase
  -- Native encoding, register reads and JALR configuration.
  signExtension : input.offset.toBitVec = match input.instruction with
    | .jal imm => SailRV32.Functions.sign_extend (m := 32) imm
    | .jalr imm => SailRV32.Functions.sign_extend (m := 32) imm
  sourceRead : input.instruction.indirect = true →
    run (SailRV32.Functions.rX_bits input.rs1) input.before = .ok input.source.toBitVec input.before
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before
  misaRead : ∃ value, run (SailRV32.readReg .misa) input.before = .ok value input.before
  landingPad : input.instruction.indirect = true →
    run (SailRV32.readReg .cur_privilege) input.before = .ok .Machine input.before ∧
    ∃ security, run (SailRV32.readReg .mseccfg) input.before = .ok security input.before ∧
      SailRV32.Functions._get_Seccfg_MLPE security = 0

end Airbender.JumpBranchSlt.Jump
