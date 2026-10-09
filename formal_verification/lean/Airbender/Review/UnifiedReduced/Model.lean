import Airbender.Review.UnifiedReduced.Artifact
import Airbender.Proofs.AddSub.RowModel

namespace Airbender.UnifiedReduced
open Airbender.Reference.RiscV
open Airbender.Arithmetic

/-- Standard arithmetic selector; x0 writes use the decoder's zero-operand ADD row. -/
def standardSelector (input : Sail.Input) : Fin 18 :=
  if input.rd = Sail.zeroRegister then 0 else
    match input.row.opcode with
    | .sub => 1
    | .auipc => 2
    | _ => 0

structure DecoderContract {p : Nat} (input : Sail.Input) (w : Nat → ZMod p) : Prop where
  active : w Variables.execute = 1
  selected : w Variables.dispatchColumns[standardSelector input] = 1
  preprocessing : AddSub.Preprocessing input

/-- The unified artifact's register-port words and canonical output limbs. -/
structure WordMapping {p : Nat} (input : Sail.Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : w 36 = (input.row.left.lo : ZMod p)
  leftHi : w 37 = (input.row.left.hi : ZMod p)
  rightLo : w 42 = (input.row.right.lo : ZMod p)
  rightHi : w 43 = (input.row.right.hi : ZMod p)
  immediateLo : w 8 = (input.row.immediate.lo : ZMod p)
  immediateHi : w 9 = (input.row.immediate.hi : ZMod p)
  pcLo : w 0 = (input.row.pc.lo : ZMod p)
  pcHi : input.row.pc.hi = (w 1).val
  destinationIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  outputLo : output.destination.lo = (w 50).val
  outputHi : output.destination.hi = (w 51).val
  finalPCLo : output.pc.lo = (w 30).val
  finalPCHi : output.pc.hi = (w 31).val

def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 10)) :
    Verification.CircuitModel Sail.Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat
    (Verification.environment w) (importedConstraints setup)
  represents := fun input output w => WordMapping input output w

/-- External inputs only; output bounds, PC advance and selector exclusivity
    follow from the imported equations and lookups. -/
structure InterfaceAssumptions {p : Nat} (input : Sail.Input)
    (_output : Sail.Output) (w : Nat → ZMod p) : Prop where
  decoder : DecoderContract input w
  ranges : input.rd ≠ Sail.zeroRegister → AddSub.InputBounds input.row
  initialPCLoBound : input.row.pc.lo < limbBase
  registers : Sail.Contract input

end Airbender.UnifiedReduced
