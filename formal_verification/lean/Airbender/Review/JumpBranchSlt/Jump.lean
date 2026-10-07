import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Review.Sail
import Airbender.Review.Properties

namespace Airbender.JumpBranchSlt.Jump
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

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

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  match input.instruction with
  | .jal imm => SailRV32.Functions.execute_JAL imm input.rd
  | .jalr imm => SailRV32.Functions.execute_JALR imm input.rs1 input.rd

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  initialPC : input.pc.lo = (w 0).val ∧ input.pc.hi = (w 1).val
  targetWords : input.base.lo = (w (if input.instruction.indirect then 22 else 0)).val ∧
    input.base.hi = (w (if input.instruction.indirect then 23 else 1)).val ∧
    w 8 = (input.offset.lo : ZMod p) ∧ w 9 = (input.offset.hi : ZMod p) ∧
    output.pc.lo = (w 16).val ∧ output.pc.hi = (w 17).val
  destination : output.destination.lo = (w 30).val ∧ output.destination.hi = (w 31).val
  rs1Index : input.instruction.indirect = true → match input.rs1 with
    | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Target/link behavior is derived from the artifact. JALR's native landing-pad
    update is disabled by explicit Machine-mode/MLPE configuration, not ignored. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  selected : w 11 = (if input.instruction.indirect then 0 else 1) ∧
    w 12 = (if input.instruction.indirect then 1 else 0)
  otherSelectors : w 13 = 0 ∧ w 14 = 0
  zeroDestination : w 15 = 1 ↔ input.rd = Sail.zeroRegister
  initialPCLoBound : input.pc.lo < limbBase
  baseLoBound : input.base.lo < limbBase
  sourceHiBound : input.instruction.indirect = true → input.base.hi < limbBase
  offsetBound : input.offset.Bounded
  directEven : input.instruction.indirect = false → input.base.lo % 2 = 0 ∧ input.offset.lo % 2 = 0
  finalPCHiBound : output.pc.hi < limbBase
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
