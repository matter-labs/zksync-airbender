module
public import Human.Circuits.Blake2Round.Artifact
public import Human.Helpers.Core.Word
public import Human.Helpers.Properties
public import Human.Circuits.Blake2Round.Control
public import Proven.Defs.Circuits.Blake2Round.Artifact

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Blake2Round/Control.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Blake2Round.Control
open Arithmetic
structure Mapping {p : Nat} (input output : Word) (w : Nat → ZMod p) : Prop where
  inputWord : input = ⟨(w Variables.controlReadLo).val, (w Variables.controlReadHi).val⟩
  outputWord : output = ⟨(w Variables.controlWriteLo).val, (w Variables.controlWriteHi).val⟩
def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 6)) :
    Verification.CircuitModel Word Word (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)
  represents := Mapping
end Airbender.Blake2Round.Control
