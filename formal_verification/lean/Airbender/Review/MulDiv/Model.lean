import Airbender.Review.MulDiv.Artifact
import Airbender.Review.Properties
import Airbender.Review.Sail

namespace Airbender.MulDiv
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

inductive Operation where
  | mul | mulhu | divu | remu

def Operation.selector : Operation → Fin 4
  | .mul => 0 | .mulhu => 1 | .divu => 2 | .remu => 3

/-- All four unsigned-family selectors, including a zero divisor. The native state is fixed external
    input; source and destination registers may alias. -/
structure Input where
  operation : Operation
  left : Word
  right : Word
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  before : Sail.State

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  match input.operation with
  | .mul => SailRV32.Functions.execute_MUL input.rs2 input.rs1 input.rd
      ⟨.Low, .Signed, .Signed⟩
  | .mulhu => SailRV32.Functions.execute_MUL input.rs2 input.rs1 input.rd
      ⟨.High, .Unsigned, .Unsigned⟩
  | .divu => SailRV32.Functions.execute_DIV input.rs2 input.rs1 input.rd true
  | .remu => SailRV32.Functions.execute_REM input.rs2 input.rs1 input.rd true

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : input.left.lo = (w 20).val
  leftHi : input.left.hi = (w 21).val
  rightLo : input.right.lo = (w 24).val
  rightHi : input.right.hi = (w 25).val
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

/-- Decoder selection, left operand bounds and successful native reads remain
    interfaces. Divisor/output bounds and the zero flag follow from lookups. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (_output : Sail.Output) (w : Nat → ZMod p) : Prop where
  selected : ∀ i : Fin 4, w (10 + i.val) = if i = input.operation.selector then 1 else 0
  leftBound : input.left.Bounded
  initialPCBound : input.pc.Bounded
  leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.left.toBitVec input.before
  rightRead : run (SailRV32.Functions.rX_bits input.rs2) input.before =
    .ok input.right.toBitVec input.before
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before

end Airbender.MulDiv
