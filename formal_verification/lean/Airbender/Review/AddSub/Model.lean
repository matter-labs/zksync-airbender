import Airbender.Review.AddSub.Artifact
import Airbender.Review.Sail
import Airbender.Review.Properties

namespace Airbender.AddSub
open Airbender.Reference.RiscV
open Airbender.Arithmetic

/-- Decoded standard row; writes to x0 select ADD with zero operands, as specified
    by Airbender's preprocessing. The original instruction tag remains unchanged in Sail. -/
structure DecoderContract {F : Type} [Field F] (input : Sail.Input) (w : Nat → F) : Prop where
  active : w 4 = 1
  addSelector : w 10 = if input.rd = Sail.zeroRegister then 1
    else if input.row.opcode = .sub ∨ input.row.opcode = .auipc then 0 else 1
  subSelector : w 11 = if input.rd ≠ Sail.zeroRegister ∧ input.row.opcode = .sub then 1 else 0
  otherSelectors : ∀ k, 12 ≤ k → k ≤ 18 →
    w k = if input.rd ≠ Sail.zeroRegister ∧ input.row.opcode = .auipc ∧ k = 12 then 1 else 0
  preprocessing : if input.rd = Sail.zeroRegister then
    input.row.left = ⟨0, 0⟩ ∧ input.row.right = ⟨0, 0⟩ ∧ input.row.immediate = ⟨0, 0⟩
    else match input.row.opcode with
      | .add | .sub => input.row.immediate = ⟨0, 0⟩
      | .addi => input.row.right = ⟨0, 0⟩
      | .lui | .auipc => input.row.left = ⟨0, 0⟩ ∧ input.row.right = ⟨0, 0⟩

/-- Operand bounds supplied by the decoder/memory interfaces. Result bounds
    follow from the imported Clean range queries. -/
structure InputBounds (input : RowInput) : Prop where
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  immediateBound : input.immediate.Bounded

/-- Inputs encode declared limbs and the destination index; outputs decode canonical prime-field values.
    This supplies no 16-bit bounds and no arithmetic conclusion. -/
structure WordMapping {p : Nat} (input : Sail.Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : w 25 = (input.row.left.lo : ZMod p)
  leftHi : w 26 = (input.row.left.hi : ZMod p)
  rightLo : w 29 = (input.row.right.lo : ZMod p)
  rightHi : w 30 = (input.row.right.hi : ZMod p)
  immediateLo : w 8 = (input.row.immediate.lo : ZMod p)
  immediateHi : w 9 = (input.row.immediate.hi : ZMod p)
  pcLo : w 0 = (input.row.pc.lo : ZMod p)
  pcHi : w 1 = (input.row.pc.hi : ZMod p)
  destinationIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  outputLo : output.destination.lo = (w 33).val
  outputHi : output.destination.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 19).val
  finalPCHi : output.pc.hi = (w 20).val

/-- PC limbs in the imported artifact. Initial bounds come from the state interface;
    final bounds are enforced by the imported lookups. -/
structure PCMapping {p : Nat} (initial final : Word) (w : Nat → ZMod p) : Prop where
  initialLo : w 0 = (initial.lo : ZMod p)
  initialHi : w 1 = (initial.hi : ZMod p)
  finalLo : final.lo = (w 19).val
  finalHi : final.hi = (w 20).val

/-- The sole constraint model: native upstream Clean operations and their
    observable mapping. External interface assumptions are listed below. -/
def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Sail.Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input output w

/-- Unproved interfaces, listed separately from the model's enforced constraints. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Sail.Input)
    (_output : Sail.Output) (w : Nat → ZMod p) : Prop where
  decoder : DecoderContract input w
  ranges : input.rd ≠ Sail.zeroRegister → InputBounds input.row
  initialPCBounds : input.row.pc.Bounded
  registers : Sail.Contract input

end Airbender.AddSub
