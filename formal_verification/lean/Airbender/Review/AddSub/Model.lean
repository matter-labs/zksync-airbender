import Airbender.Review.AddSub.Artifact
import Airbender.Review.Sail
import Airbender.Review.Properties

namespace Airbender.AddSub
open Airbender.Reference.RiscV
open Airbender.Arithmetic

/-- These assumptions select a decoded ADD/ADDI/SUB row. They do not assert an ALU result. -/
structure DecoderContract {F : Type} [Field F] (input : RowInput) (w : Nat → F) : Prop where
  active : w 4 = 1
  addSelector : w 10 = if input.opcode = .sub then 0 else 1
  subSelector : w 11 = if input.opcode = .sub then 1 else 0
  otherSelectors : ∀ k, 12 ≤ k → k ≤ 16 → w k = 0
  preprocessing : match input.opcode with
    | .add | .sub => input.immediate = ⟨0, 0⟩
    | .addi => input.right = ⟨0, 0⟩

/-- Operand bounds supplied by the decoder/memory interfaces. Result bounds
    follow from the imported Clean range queries. -/
structure InputBounds (input : RowInput) : Prop where
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  immediateBound : input.immediate.Bounded

/-- Inputs encode declared limbs; outputs decode canonical prime-field values.
    This supplies no 16-bit bounds and no arithmetic conclusion. -/
structure WordMapping {p : Nat} (input : RowInput) (output : Word)
    (w : Nat → ZMod p) : Prop where
  leftLo : w 25 = (input.left.lo : ZMod p)
  leftHi : w 26 = (input.left.hi : ZMod p)
  rightLo : w 29 = (input.right.lo : ZMod p)
  rightHi : w 30 = (input.right.hi : ZMod p)
  immediateLo : w 8 = (input.immediate.lo : ZMod p)
  immediateHi : w 9 = (input.immediate.hi : ZMod p)
  outputLo : output.lo = (w 33).val
  outputHi : output.hi = (w 34).val

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
    Verification.CircuitModel Sail.Input Word (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input.row output w

/-- Unproved interfaces, listed separately from the model's enforced constraints. -/
structure InterfaceAssumptions {p : Nat} [Fact p.Prime] (input : Sail.Input)
    (_output : Word) (w : Nat → ZMod p) : Prop where
  decoder : DecoderContract input.row w
  ranges : InputBounds input.row
  registers : Sail.Contract input

end Airbender.AddSub
