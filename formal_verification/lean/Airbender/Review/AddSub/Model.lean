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

/-- External range/lookup obligations. These bounds are assumed by this pilot;
    they are not yet derived from a verified lookup argument. -/
structure WordBounds (input : RowInput) (output : Word) : Prop where
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  immediateBound : input.immediate.Bounded
  outputBound : output.Bounded

/-- Representation mapping only: named JSON variables denote the declared words.
    This supplies no bounds and no arithmetic conclusion. -/
structure WordMapping {F : Type} [Field F] (input : RowInput) (output : Word)
    (w : Nat → F) : Prop where
  leftLo : w 25 = (input.left.lo : F)
  leftHi : w 26 = (input.left.hi : F)
  rightLo : w 29 = (input.right.lo : F)
  rightHi : w 30 = (input.right.hi : F)
  immediateLo : w 8 = (input.immediate.lo : F)
  immediateHi : w 9 = (input.immediate.hi : F)
  outputLo : w 33 = (output.lo : F)
  outputHi : w 34 = (output.hi : F)

/-- The sole constraint model: native upstream Clean operations and their
    observable mapping. No decoder/range/register assumptions are bundled here. -/
def circuitModel {F : Type} [FiniteField F] :
    Verification.CircuitModel Sail.Input Word (Nat → F) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => WordMapping input.row output w

/-- Unproved interfaces, listed separately from the model's enforced equations. -/
structure InterfaceAssumptions {F : Type} [FiniteField F] (input : Sail.Input)
    (output : Word) (w : Nat → F) : Prop where
  decoder : DecoderContract input.row w
  ranges : WordBounds input.row output
  registers : Sail.Contract input

end Airbender.AddSub
