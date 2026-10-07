import Airbender.Review.MulDiv.Artifact
import Airbender.Review.Properties
import Airbender.Review.Sail

namespace Airbender.MulDiv.ZeroDivision
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

/-- First M-extension slice: DIVU/REMU with a zero divisor. The state is fixed
    external input; source and destination registers may alias. -/
structure Input where
  remainder : Bool
  left : Word
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  before : Sail.State

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  if input.remainder then SailRV32.Functions.execute_REM input.rs2 input.rs1 input.rd true
  else SailRV32.Functions.execute_DIV input.rs2 input.rs1 input.rd true

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : input.left.lo = (w 20).val
  leftHi : input.left.hi = (w 21).val
  divisorZero : w 24 = 0 ∧ w 25 = 0
  rs1Index : match input.rs1 with | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w 6 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : w 0 = (input.pc.lo : ZMod p)
  pcHi : w 1 = (input.pc.hi : ZMod p)
  outputLo : output.destination.lo = (w 28).val
  outputHi : output.destination.hi = (w 29).val
  finalPCLo : output.pc.lo = (w 14).val
  finalPCHi : output.pc.hi = (w 15).val

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Decoder selection and successful native reads remain interfaces. The zero
    divisor is this slice's input domain; no desired result or zero flag is assumed. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (_output : Sail.Output) (w : Nat → ZMod p) : Prop where
  selected : w 12 = (if input.remainder then 0 else 1) ∧
    w 13 = (if input.remainder then 1 else 0)
  otherSelectors : w 10 = 0 ∧ w 11 = 0
  initialPCBound : input.pc.Bounded
  leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.left.toBitVec input.before
  rightRead : run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok 0 input.before
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before

end Airbender.MulDiv.ZeroDivision
