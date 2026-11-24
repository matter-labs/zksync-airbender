module
public import Human.Circuits.Bigint.Artifact
public import Human.Circuits.Bigint.Word
public import Human.Circuits.Bigint.Tables.Setup
public import Human.Helpers.Properties
public import Human.Circuits.Bigint.Multiplication

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Bigint/Multiplication.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Bigint.Multiplication
open Arithmetic
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  selected : w Variables.operations[input.operation.index] = 1
  left : ∀ i : Fin 16, input.left[i] = (w Variables.leftLimbs[i]).val
  right : ∀ i : Fin 16, input.right[i] = (w Variables.rightLimbs[i]).val
  result : ∀ i : Fin 16, output.result[i] = (w Variables.writtenLimbs[i]).val
  control : output.control = ⟨(w 57).val, (w 58).val⟩
/-- All ranges come from native queries against the modeled production setup.
    Its connection to Rust generation remains the shared provenance gap. -/
def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setupTable)
  represents := Mapping
end Airbender.Bigint.Multiplication
