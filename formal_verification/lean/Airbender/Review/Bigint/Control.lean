import Airbender.Review.Bigint.Artifact
import Airbender.Review.Word
import Airbender.Review.Properties

namespace Airbender.Bigint.Control
open Arithmetic
open scoped BigOperators

structure Output where
  register : Word
  bits : Vector Bool 8

/-- ABI order: add, sub, reversed sub, low product, high product, equality,
    carry/borrow, copy. Source: common_constants/src/delegation_types/bigint_with_control.rs. -/
def mask (bits : Vector Bool 8) : Nat := ∑ i : Fin 8, 2 ^ i.val * bits[i].toNat

def operationCount (bits : Vector Bool 8) : Nat :=
  ∑ i : Fin 7, bits[(#v[0, 1, 2, 3, 4, 5, 7] : Vector (Fin 8) 7)[i]].toNat

/-- Local control guarantees only. Incoming x12's high limb is ignored by this
    circuit; carry/borrow is independent of opcode selection. Arithmetic results
    and the meaning of the returned low limb need subsequent operation proofs. -/
def spec (input : Word) (output : Output) : Prop :=
  input.lo = mask output.bits ∧ input.lo < 256 ∧
  operationCount output.bits ≤ 1 ∧ output.register.hi = 0

structure Mapping {p : Nat} (input : Word) (output : Output) (w : Nat → ZMod p) : Prop where
  inputWord : input = ⟨(w 55).val, (w 56).val⟩
  outputWord : output.register = ⟨(w 57).val, (w 58).val⟩
  bits : output.bits = Vector.ofFn (fun i => (w Variables.controlBits[i]).val == 1)

-- This claim holds for arbitrary supplied rows: no fixed-table semantics or
-- external decoder/read/range premise is needed to prove control validity.
def circuitModel {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 3)) :
    Verification.CircuitModel Word Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setup)
  represents := Mapping

end Airbender.Bigint.Control
