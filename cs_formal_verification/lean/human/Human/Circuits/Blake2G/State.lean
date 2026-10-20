import Human.Circuits.Blake2G.Control

namespace Airbender.Blake2G.State
open Arithmetic

structure Input where
  state : Vector Word 16
  lanes : Vector (Fin 16) 4
  mx : Word
  my : Word

abbrev Output := Vector Word 16

def mixingInput (input : Input) : Blake2G.Input :=
  ⟨⟨input.state[input.lanes[0]], input.state[input.lanes[1]],
      input.state[input.lanes[2]], input.state[input.lanes[3]]⟩, input.mx, input.my⟩

def mixingOutput (input : Input) (output : Output) : Words :=
  ⟨output[input.lanes[0]], output[input.lanes[1]],
    output[input.lanes[2]], output[input.lanes[3]]⟩

/-- The full state is compared directly with Clean's G at the selected lanes;
    there is no replacement mixing specification. -/
def spec (input : Input) (output : Output) : Prop :=
  output.map Word.value = Specs.BLAKE3.g (input.state.map Word.value)
    input.lanes[0] input.lanes[1] input.lanes[2] input.lanes[3] input.mx.value input.my.value

/-- Bind selected words to the actual four read/write ports, and lane identities
    to their imported controller columns. Message-word selection is separate. -/
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  words : WordMapping (mixingInput input) (mixingOutput input output) w
  laneSelection : ∀ i : Fin 4, (w Variables.stateOffsetColumns[i]).val = input.lanes[i].val

/-- The memory interface supplies reads/writes at the mapped ports and leaves
    all other lanes unchanged. The four arithmetic input bounds are unchanged
    from the mixing theorem. The control bound is the eight-bit ABI domain;
    lane distinctness follows from the lookup. No G result is assumed. -/
structure InterfaceAssumptions {p : Nat} (input : Input) (output : Output)
    (w : Nat → ZMod p) : Prop where
  active : w Variables.execute = 1
  controlBound : (w Variables.controlReadLo).val < 256
  inputs : Blake2G.InterfaceAssumptions (mixingInput input) (mixingOutput input output) w
  untouched : ∀ i : Fin 16, (∀ j : Fin 4, i ≠ input.lanes[j]) → output[i] = input.state[i]

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints (setupTable Control.controllerRows))
  represents := Mapping

end Airbender.Blake2G.State
