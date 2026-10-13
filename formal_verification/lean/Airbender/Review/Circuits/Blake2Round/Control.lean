import Airbender.Review.Circuits.Blake2Round.Artifact
import Airbender.Review.Helpers.Word
import Airbender.Review.Helpers.Properties

namespace Airbender.Blake2Round.Control
open Arithmetic

/-- The caller selects exactly one of the ten native round bits.
    Individual bit checks in the artifact do not establish this ABI condition. -/
def RoundMask {p : Nat} (w : Nat → ZMod p) (round : Fin 10) : Prop :=
  ∀ i : Fin 10, w Variables.roundBits[i] = if i = round then 1 else 0

/-- x12 update in `blake2_round_with_extended_control/mod.rs`: clear the low
    limb, retain the three control bits, shift the ten round bits and drop the
    last one. This local claim does not require an exclusive round mask. -/
def next (input : Word) : Word :=
  ⟨0, input.hi % 8 + 16 * (input.hi / 8 % 512)⟩

def spec (input output : Word) : Prop := input.hi < 8192 ∧ output = next input

structure Mapping {p : Nat} (input output : Word) (w : Nat → ZMod p) : Prop where
  inputWord : input = ⟨(w Variables.controlReadLo).val, (w Variables.controlReadHi).val⟩
  outputWord : output = ⟨(w Variables.controlWriteLo).val, (w Variables.controlWriteHi).val⟩

-- The control claim holds for any supplied XOR setup. Its behavior does not
-- depend on lookup-table contents; the whole round will use concrete XOR semantics.
def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4)) :
    Verification.CircuitModel Word Word (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)
  represents := Mapping

end Airbender.Blake2Round.Control
