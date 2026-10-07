import Airbender.Review.ShiftBinop.Artifact
import Airbender.Review.Properties
import Airbender.Review.Sail

namespace Airbender.ShiftBinop
open Airbender.Arithmetic
open Airbender.Reference.RiscV
open Airbender.Reference.Sail

inductive Operation where
  | xor | or | and
  deriving DecidableEq

def Operation.tag : Operation → Nat
  | .xor => 4 | .or => 6 | .and => 7

/-- Native source words; `right` is rs2 or the sign-extended immediate.
    The initial state is fixed input. Source and destination registers may alias. -/
structure Input where
  operation : Operation
  immediate : Bool
  left : BitVec 32
  right : BitVec 32
  pc : Word
  rs1 : SailRV32.regidx
  rs2 : SailRV32.regidx
  rd : SailRV32.regidx
  encodedImmediate : BitVec 12
  before : Sail.State

def execution (input : Input) : SailRV32.SailM SailRV32.ExecutionResult :=
  if input.immediate then
    SailRV32.Functions.execute_ITYPE input.encodedImmediate input.rs1 input.rd
      (match input.operation with | .xor => .XORI | .or => .ORI | .and => .ANDI)
  else
    SailRV32.Functions.execute_RTYPE input.rs2 input.rs1 input.rd
      (match input.operation with | .xor => .XOR | .or => .OR | .and => .AND)

abbrev spec (input : Input) (output : Sail.Output) : Prop :=
  Sail.stepSpec input.before (execution input) input.rd output

/-- Query inputs include the decoder's packed immediate and sign-extension byte.
    This maps bytes to native operands; it does not prescribe the result. -/
structure WordMapping {p : Nat} (input : Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftBytes : ∀ i : Fin 4,
    w (19 + i.val) = ((input.left.extractLsb' (8 * i.val) 8).toNat : ZMod p)
  rightBytes : ∀ i : Fin 4,
    w (25 + i.val) + (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35) =
      ((input.right.extractLsb' (8 * i.val) 8).toNat : ZMod p)
  rs1Index : match input.rs1 with | .Regidx bits => w 5 = (bits.toNat : ZMod p)
  rs2Index : match input.rs2 with | .Regidx bits => w 6 = (bits.toNat : ZMod p)
  rdIndex : match input.rd with | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  pcLo : w 0 = (input.pc.lo : ZMod p)
  pcHi : w 1 = (input.pc.hi : ZMod p)
  outputLo : output.destination.lo = (w 31).val
  outputHi : output.destination.hi = (w 32).val
  finalPCLo : output.pc.lo = (w 13).val
  finalPCHi : output.pc.hi = (w 14).val

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Decoder selection and successful native reads remain interfaces. Operand and
    destination byte bounds follow from lookups, so no operand ranges are assumed. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Input)
    (_output : Sail.Output) (w : Nat → ZMod p) : Prop where
  active : w 4 = 1
  selected : w 11 = 0 ∧ w 12 = 1
  funct3 : w 10 = (input.operation.tag : ZMod p)
  nonzeroDestination : input.rd ≠ Sail.zeroRegister
  initialPCBound : input.pc.Bounded
  leftRead : run (SailRV32.Functions.rX_bits input.rs1) input.before =
    .ok input.left input.before
  rightRead : input.immediate = false →
    run (SailRV32.Functions.rX_bits input.rs2) input.before = .ok input.right input.before
  signExtension : input.immediate = true →
    input.right = SailRV32.Functions.sign_extend (m := 32) input.encodedImmediate
  pcRead : run (SailRV32.Functions.get_arch_pc ()) input.before = .ok input.pc.toBitVec input.before

end Airbender.ShiftBinop
