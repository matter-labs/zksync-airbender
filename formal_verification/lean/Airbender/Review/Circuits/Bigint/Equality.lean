import Airbender.Review.Circuits.Bigint.Artifact
import Airbender.Review.Circuits.Bigint.Word
import Airbender.Review.Helpers.Properties

namespace Airbender.Bigint.Equality
open Arithmetic

structure Input where
  left : Vector Nat 16
  right : Vector Nat 16

/-- EQ in `bigint_impl` (`riscv_transpiler/src/vm/delegations/bigint.rs`):
    preserve the left operand and return its equality to the right in x12.
    The incoming carry bit is ignored. This is a handwritten custom reference,
    not a standard Sail clause or a full memory/CSR-call claim. -/
def spec (input : Input) (output : Output) : Prop :=
  output.result = input.left ∧
  output.control = ⟨if input.left = input.right then 1 else 0, 0⟩

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
