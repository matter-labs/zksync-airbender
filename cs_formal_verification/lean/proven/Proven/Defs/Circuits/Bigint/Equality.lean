module
public import Human.Circuits.Bigint.Artifact
public import Human.Circuits.Bigint.Word
public import Human.Helpers.Properties
public import Human.Circuits.Bigint.Equality

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Bigint/Equality.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Bigint.Equality
open Arithmetic
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  selected : w 64 = 1
  left : ∀ i : Fin 16, input.left[i] = (w Variables.leftLimbs[i]).val
  right : ∀ i : Fin 16, input.right[i] = (w Variables.rightLimbs[i]).val
  result : ∀ i : Fin 16, output.result[i] = (w Variables.writtenLimbs[i]).val
  control : output.control = ⟨(w 57).val, (w 58).val⟩
/-- Source ranges are external for arbitrary setups and derived for the
    modeled setup. Comparison, carries and preservation follow from the row. -/
def InterfaceAssumptions (input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop :=
  (∀ i : Fin 16, input.left[i] < limbBase) ∧ (∀ i : Fin 16, input.right[i] < limbBase)
def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)
  represents := Mapping
end Airbender.Bigint.Equality
