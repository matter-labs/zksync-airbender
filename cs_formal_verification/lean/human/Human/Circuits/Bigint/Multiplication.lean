import Human.Circuits.Bigint.Artifact
import Human.Circuits.Bigint.Word
import Human.Circuits.Bigint.Tables.Setup
import Human.Helpers.Properties

namespace Airbender.Bigint.Multiplication
open Arithmetic

inductive Operation
  | low | high
  deriving DecidableEq

def Operation.index : Operation → Fin 7
  | .low => 3 | .high => 4

structure Input where
  operation : Operation
  left : Vector Nat 16
  right : Vector Nat 16

/-- MUL_LOW/MUL_HIGH in the project's `bigint_impl`
    (`riscv_transpiler/src/vm/delegations/bigint.rs`). Low returns overflow;
    high returns zero. Both ignore incoming carry. This custom reference needs
    review and does not specify the surrounding memory/CSR call. -/
def spec (input : Input) (output : Output) : Prop :=
  let product := value input.left * value input.right
  (∀ i : Fin 16, output.result[i] < limbBase) ∧
    value output.result = (match input.operation with
      | .low => product % 2 ^ 256
      | .high => product / 2 ^ 256) ∧
    output.control = ⟨match input.operation with
      | .low => if 2 ^ 256 ≤ product then 1 else 0
      | .high => 0, 0⟩

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
