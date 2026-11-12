module
public import Human.Circuits.Blake2Round.Artifact
public import Human.Helpers.Core.Word
public import Human.Helpers.Properties

@[expose] public section

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

-- The control claim holds for any supplied XOR setup. Its behavior does not
-- depend on lookup-table contents; the whole round will use concrete XOR semantics.

end Airbender.Blake2Round.Control
