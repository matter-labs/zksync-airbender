import Human.Circuits.Bigint.Additive
import Human.Circuits.Bigint.Equality
import Human.Circuits.Bigint.Multiplication
import Human.Helpers.Delegation.WorkerContext

namespace Airbender.Bigint.Native

/-- Canonical limbs observed at the native bigint ports. The column arrays
    already name the JSON's left reads, right reads and destination writes. -/
def limbs (w : Nat → ZMod p) (columns : Vector Nat 16) : Vector Nat 16 :=
  columns.map fun column => (w column).val

/-- The actual written block and x12 response, shared by all seven operations. -/
def output (w : Nat → ZMod p) : Output :=
  ⟨limbs w Variables.writtenLimbs, ⟨(w 57).val, (w 58).val⟩⟩

/-- Reuse the existing project references with operands observed from the
    native ports. These definitions identify values; they impose no behavior. -/
def additiveInput (operation : Additive.Operation) (w : Nat → ZMod p) : Additive.Input :=
  ⟨operation, limbs w Variables.leftLimbs, limbs w Variables.rightLimbs, (w 65).val == 1⟩

def equalityInput (w : Nat → ZMod p) : Equality.Input :=
  ⟨limbs w Variables.leftLimbs, limbs w Variables.rightLimbs⟩

def multiplicationInput (operation : Multiplication.Operation) (w : Nat → ZMod p) : Multiplication.Input :=
  ⟨operation, limbs w Variables.leftLimbs, limbs w Variables.rightLimbs⟩

/-- Each selected branch agrees with its existing arithmetic reference.
    The shared execution claim additionally realizes these same port values in
    actual Sail read/write states. This covers operation effects, not caller ABI:
    no-opcode rows remain the separately flagged local circuit mismatch. -/
def ArithmeticEffects (w : Nat → ZMod p) : Prop :=
  (∀ operation, w Variables.operations[operation.index] = 1 →
    Additive.spec (additiveInput operation w) (output w)) ∧
  (w 64 = 1 → Equality.spec (equalityInput w) (output w)) ∧
  (∀ operation, w Variables.operations[operation.index] = 1 →
    Multiplication.spec (multiplicationInput operation w) (output w))

end Airbender.Bigint.Native
