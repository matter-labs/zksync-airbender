import Airbender.Review.Blake2G.Artifact
import Airbender.Review.Blake2G.Tables
import Airbender.Review.Properties
import Airbender.Review.Word
import Clean.Specs.BLAKE3

namespace Airbender.Blake2G

open Arithmetic

structure Words where
  a : Word
  b : Word
  c : Word
  d : Word

structure Input where
  state : Words
  mx : Word
  my : Word

/-- Reuse Clean's actual G function. Its mixing operation is shared by BLAKE2s
    and BLAKE3; this claim does not cover either hash's complete compression. -/
def spec (input : Input) (output : Words) : Prop :=
  -- The other twelve lanes are unused by this G invocation.
  let initial := #v[input.state.a.value, input.state.b.value, input.state.c.value,
    input.state.d.value, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  let result := Specs.BLAKE3.g initial ⟨0, by decide⟩ ⟨1, by decide⟩
    ⟨2, by decide⟩ ⟨3, by decide⟩ input.mx.value input.my.value
  output.a.value = result[0] ∧ output.b.value = result[1] ∧
    output.c.value = result[2] ∧ output.d.value = result[3]

/-- Bind the six incoming words and four outgoing words to their imported
    indirect-memory ports. Address selection and transport are separate tasks. -/
structure WordMapping {p : Nat} (input : Input) (output : Words)
    (w : Nat → ZMod p) : Prop where
  stateReads : input.state =
    ⟨⟨(w 15).val, (w 16).val⟩, ⟨(w 19).val, (w 20).val⟩,
      ⟨(w 23).val, (w 24).val⟩, ⟨(w 27).val, (w 28).val⟩⟩
  messageX : input.mx = ⟨(w 33).val, (w 34).val⟩
  messageY : input.my = ⟨(w 35).val, (w 36).val⟩
  stateWrites : output =
    ⟨⟨(w 17).val, (w 18).val⟩, ⟨(w 21).val, (w 22).val⟩,
      ⟨(w 25).val, (w 26).val⟩, ⟨(w 29).val, (w 30).val⟩⟩

/-- Only these four input-word bounds remain external. The imported queries
    establish b/d input bounds and all intermediate/output bounds. -/
structure InterfaceAssumptions {p : Nat} (input : Input) (_output : Words)
    (_w : Nat → ZMod p) : Prop where
  aBound : input.state.a.Bounded
  cBound : input.state.c.Bounded
  messageXBound : input.mx.Bounded
  messageYBound : input.my.Bounded

def circuitModel {p : Nat} [Fact p.Prime] (control : Fin 512 → Vector Nat 7) :
    Verification.CircuitModel Input Words (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat
    (Verification.environment w) (importedConstraints (setupTable control))
  represents := WordMapping

end Airbender.Blake2G
