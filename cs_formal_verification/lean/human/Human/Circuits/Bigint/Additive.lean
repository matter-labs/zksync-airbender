module
public import Human.Circuits.Bigint.Artifact
public import Human.Helpers.Core.Word
public import Human.Helpers.Properties
public import Human.Circuits.Bigint.Word

@[expose] public section

namespace Airbender.Bigint.Additive
open Arithmetic
open scoped BigOperators

inductive Operation
  | add | sub | reverseSub | copy
  deriving DecidableEq

def Operation.index : Operation → Fin 7
  | .add => 0 | .sub => 1 | .reverseSub => 2 | .copy => 6

structure Input where
  operation : Operation
  left : Vector Nat 16
  right : Vector Nat 16
  carry : Bool

/-- Arithmetic clauses of the project's `bigint_impl` in
    `riscv_transpiler/src/vm/delegations/bigint.rs`: x12 returns carry/borrow.
    Copy also adds the incoming carry. This custom reference needs review;
    it is not a standard Sail instruction or a full memory/CSR call claim. -/
def spec (input : Input) (output : Output) : Prop :=
  (∀ i : Fin 16, output.result[i] < limbBase) ∧
  output.control.lo ≤ 1 ∧ output.control.hi = 0 ∧
  match input.operation with
  | .add => value input.left + value input.right + input.carry.toNat =
      value output.result + 2 ^ 256 * output.control.lo
  | .sub => value output.result + value input.right + input.carry.toNat =
      value input.left + 2 ^ 256 * output.control.lo
  | .reverseSub => value output.result + value input.left + input.carry.toNat =
      value input.right + 2 ^ 256 * output.control.lo
  | .copy => value input.right + input.carry.toNat =
      value output.result + 2 ^ 256 * output.control.lo

end Airbender.Bigint.Additive
