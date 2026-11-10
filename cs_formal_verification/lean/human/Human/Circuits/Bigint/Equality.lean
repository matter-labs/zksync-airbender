module
public import Human.Circuits.Bigint.Artifact
public import Human.Circuits.Bigint.Word
public import Human.Helpers.Properties

@[expose] public section

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

end Airbender.Bigint.Equality
