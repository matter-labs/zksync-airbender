module
public import Slop.Defs.Circuits.Bigint.Control
public import Human.Circuits.Bigint.Word
public import Human.Circuits.Bigint.Additive

/-! Definitions only the proofs use, moved from `human/Human/Circuits/Bigint/Additive.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Bigint.Additive
open Arithmetic
open scoped BigOperators
/-- Source/destination limbs are canonical observations of actual memory ports.
    The selected opcode and incoming carry identify the requested branch. -/
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  selected : w Variables.operations[input.operation.index] = 1
  carry : w 65 = if input.carry then 1 else 0
  left : ∀ i : Fin 16, input.left[i] = (w Variables.leftLimbs[i]).val
  right : ∀ i : Fin 16, input.right[i] = (w Variables.rightLimbs[i]).val
  result : ∀ i : Fin 16, output.result[i] = (w Variables.writtenLimbs[i]).val
  control : output.control = ⟨(w 57).val, (w 58).val⟩
/-- Arbitrary supplied setups need input ranges. The modeled-setup theorem
    derives these from native lookups; result ranges and carries are local. -/
def InterfaceAssumptions (input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop :=
  (∀ i : Fin 16, input.left[i] < limbBase) ∧ (∀ i : Fin 16, input.right[i] < limbBase)
def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)
  represents := Mapping
end Airbender.Bigint.Additive
