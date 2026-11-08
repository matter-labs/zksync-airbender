import Slop.MulDiv.Product
import Human.Circuits.MulDiv.Operation
import Human.Helpers.Context.RowContext
import Human.Helpers.Decoder.PooledProgram
import Human.Helpers.Tables.Subword
import Human.Circuits.AddSub.RowInput
import Mathlib.Tactic.IntervalCases

namespace Airbender.MulDiv.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV

-- These arithmetic expressions are proof intermediates; the public reference
-- remains the original Sail execution in Review/MulDiv/Model.lean.
private def result (operation : Operation) (left right : Nat) : Nat :=
  match operation with
  | .mul => (left * right) % wordModulus
  | .mulhu => (left * right) / wordModulus
  | .divu => if right = 0 then 4294967295 else left / right
  | .remu => if right = 0 then left else left % right

private theorem division_destination {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (remainder : Bool)
    (selected : w 12 = (if remainder then 0 else 1) ∧ w 13 = (if remainder then 1 else 0))
    (other : w 10 = 0 ∧ w 11 = 0)
    (leftBound : (w 20).val < limbBase ∧ (w 21).val < limbBase) :
    (⟨(w 28).val, (w 29).val⟩ : Word).toBitVec = BitVec.ofNat 32
      (if (⟨(w 24).val, (w 25).val⟩ : Word).value = 0 then
        if remainder then (⟨(w 20).val, (w 21).val⟩ : Word).value else 4294967295
      else if remainder then (⟨(w 20).val, (w 21).val⟩ : Word).value %
        (⟨(w 24).val, (w 25).val⟩ : Word).value
      else (⟨(w 20).val, (w 21).val⟩ : Word).value /
        (⟨(w 24).val, (w 25).val⟩ : Word).value) := by
  by_cases zero : (⟨(w 24).val, (w 25).val⟩ : Word).value = 0
  · have zeroFields : w 24 = 0 ∧ w 25 = 0 := by
      simpa [Word.value, limbBase, ZMod.val_eq_zero] using zero
    have value := division_by_zero (by omega) remainder h selected other zeroFields
    cases remainder <;> simpa [zero, Word.toBitVec] using value
  · have value := division_nonzero hp inverse h remainder selected other leftBound zero
    simp only [ite_eq_right zero, Word.toBitVec, value]

end Airbender.MulDiv.Proofs
