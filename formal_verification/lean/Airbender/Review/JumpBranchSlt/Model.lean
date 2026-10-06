import Airbender.Review.JumpBranchSlt.Artifact
import Airbender.Review.Sail
import Airbender.Review.Properties

namespace Airbender.JumpBranchSlt.Sltu
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

/-- Fixed architectural input for SLTU; registers may alias. Writes to x0 are
    preprocessed into the ADD/SUB family and are outside this slice. -/
structure Input where
  left : Word
  right : Word
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  before : Sail.State

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd .SLTU

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Operand encodings, native register indices and canonical PC/output decoding.
    This identifies observables without asserting instruction behavior. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : w 22 = (input.left.lo : ZMod p)
  leftHi : w 23 = (input.left.hi : ZMod p)
  rightLo : w 26 = (input.right.lo : ZMod p)
  rightHi : w 27 = (input.right.hi : ZMod p)
  rs1Index : match input.rs1 with
    | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with
    | .Regidx bits => w 6 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : input.pc.lo = (w 0).val
  pcHi : input.pc.hi = (w 1).val
  outputLo : output.destination.lo = (w 30).val
  outputHi : output.destination.hi = (w 31).val
  finalPCLo : output.pc.lo = (w 16).val
  finalPCHi : output.pc.hi = (w 17).val

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Decoder and register/state interfaces, not consequences of the local circuit.
    Lookups bound the initial high PC limb and intermediate low PC. The final
    high limb is not range-checked here; its bound remains an explicit obligation. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (output : Sail.Output) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  selected : w 13 = 1
  otherSelectors : w 11 = 0 ∧ w 12 = 0 ∧ w 14 = 0
  immediate : w 8 = 0 ∧ w 9 = 0
  funct3 : w 10 = 3
  nonzeroSelector : w 15 = 0
  nonzeroDestination : input.rd ≠ Sail.zeroRegister
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  initialPCLoBound : input.pc.lo < limbBase
  pcAligned : input.pc.lo % 4 = 0
  finalPCHiBound : output.pc.hi < limbBase
  leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.left.toBitVec input.before
  rightRead : run (SailRV32.Functions.rX_bits input.rs2) input.before =
    .ok input.right.toBitVec input.before
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before =
    .ok input.pc.toBitVec input.before

end Airbender.JumpBranchSlt.Sltu
