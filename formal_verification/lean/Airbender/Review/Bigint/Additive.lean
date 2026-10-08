import Airbender.Review.Bigint.Control
import Airbender.Review.Bigint.Word

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
