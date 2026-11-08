module
public import Slop.ShiftBinop
public import Slop.ShiftBinop.Shifts
public import Slop.ByteTables
public import Slop.Arithmetic.Bytes
public import Human.Helpers.Context.RowContext
public import Human.Helpers.Decoder.PooledProgram
public import Human.Circuits.AddSub.RowInput

@[expose] public section

namespace Airbender.ShiftBinop.Proofs
open Airbender.Arithmetic
open Airbender.Reference.RiscV

private theorem wiring {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) :
    ∀ i : Fin 4,
      w (56 + 9 * i.val) = w (19 + i.val) ∧
      w (57 + 9 * i.val) = w (25 + i.val) +
        (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35) ∧
      w (58 + 9 * i.val) = w (36 + i.val) ∧
      w (64 + 9 * i.val) = w 10 := by
  intro i
  have a := Verification.assertion_of_holds h
    ⟨5 + 9 * i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have b := Verification.assertion_of_holds h
    ⟨6 + 9 * i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have c := Verification.assertion_of_holds h
    ⟨7 + 9 * i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have t := Verification.assertion_of_holds h
    ⟨13 + 9 * i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  fin_cases i <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected.1, selected.2] at a b c t ⊢
  all_goals
    repeat' apply And.intro
    all_goals solve | linear_combination a | linear_combination b |
      linear_combination c | linear_combination t

/-- The imported byte query enforces both source bounds and the output byte.
    Shared by the local ISA proof and native port interpretation. -/
theorem binary_query_values {p : Nat} [Fact p.Prime] (hp : 256 < p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (selected : w 11 = 0 ∧ w 12 = 1) (tag : Nat)
    (validTag : tag = 4 ∨ tag = 6 ∨ tag = 7) (funct3 : w 10 = (tag : ZMod p))
    (i : Fin 4) : (w (19 + i.val)).val < 256 ∧
      (w (25 + i.val) + (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35)).val < 256 ∧
      (w (36 + i.val)).val < 256 ∧ BitVec.ofNat 8 (w (36 + i.val)).val =
        Verification.byteOperation tag (BitVec.ofNat 8 (w (19 + i.val)).val)
          (BitVec.ofNat 8 (w (25 + i.val) +
            (if i.val = 0 then w 8 else if i.val = 1 then w 9 else w 35)).val) := by
  have wires := wiring h selected i
  have query := Verification.lookup_of_holds h
    ⟨3 + i.val, by rw [lookup_count]; have := i.isLt; omega⟩
  fin_cases i
  all_goals
    norm_num only at wires
    have value := Verification.binary_lookup hp query tag validTag
      (by simpa [Expression.eval, Verification.environment, wires.2.2.2] using funct3)
    simpa [Expression.eval, Verification.environment, wires.1, wires.2.1,
      wires.2.2.1] using value

end Airbender.ShiftBinop.Proofs
