module
public import Human.Circuits.Bigint.Artifact
public import Human.Circuits.Bigint.Word
public import Human.Circuits.Bigint.Tables.Setup
public import Human.Helpers.Properties

@[expose] public section

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

end Airbender.Bigint.Multiplication
