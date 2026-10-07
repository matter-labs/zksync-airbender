import Airbender.Proofs.MulDiv
import Airbender.Proofs.Arithmetic.Multiplication

namespace Airbender.MulDiv.Proofs
open Airbender.Arithmetic

private def roleSources : Fin 4 → Vector (Option Nat) 8
  | 0 => #v[some 28, some 29, some 37, some 38, none, none, some 24, some 25]
  | 1 => #v[some 37, some 38, some 28, some 29, none, none, some 24, some 25]
  | 2 => #v[some 20, some 21, none, none, some 37, some 38, some 24, some 25]
  | 3 => #v[some 20, some 21, none, none, some 28, some 29, some 24, some 25]

private theorem product_wiring {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (operation : Fin 4)
    (selected : ∀ i : Fin 4, w (10 + i.val) = if i = operation then 1 else 0) :
    ∀ i : Fin 8, w ([45, 46, 47, 48, 51, 52, 53, 54].get i) =
      match (roleSources operation).get i with | some v => w v | none => 0 := by
  intro i
  let index := [2, 3, 4, 5, 8, 9, 10, 11].get i
  have equation := Verification.assertion_of_holds h
    ⟨index, by dsimp [index]; fin_cases i <;> rw [constraint_count] <;> decide⟩
  have s0 := selected ⟨0, by decide⟩
  have s1 := selected ⟨1, by decide⟩
  have s2 := selected ⟨2, by decide⟩
  have s3 := selected ⟨3, by decide⟩
  fin_cases operation <;> fin_cases i <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, index, roleSources, Vector.get] at s0 s1 s2 s3 equation ⊢ <;>
    simp [s0, s1, s2, s3] at equation <;> linear_combination equation

/-- Exact integer product, proved by lifting each bounded byte column separately.
    Selector order is MUL, MULHU, DIVU, REMU. The dividend/input limb bounds
    remain a register interface; no product, quotient or remainder is assumed. -/
theorem product_with_remainder {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (operation : Fin 4)
    (selected : ∀ i : Fin 4, w (10 + i.val) = if i = operation then 1 else 0)
    (leftBound : (w 20).val < limbBase ∧ (w 21).val < limbBase) :
    (⟨(w 49).val, (w 50).val⟩ : Word).value *
        (⟨(w 24).val, (w 25).val⟩ : Word).value +
      (⟨(w 51).val, (w 52).val⟩ : Word).value =
      (⟨(w 45).val, (w 46).val⟩ : Word).value + wordModulus *
        (⟨(w 47).val, (w 48).val⟩ : Word).value := by
  have roles := product_wiring h operation selected
  have ranges := local_ranges h
  have b28 := ranges ⟨0, by decide⟩
  have b29 := ranges ⟨1, by decide⟩
  have b37 := ranges ⟨2, by decide⟩
  have b38 := ranges ⟨3, by decide⟩
  dsimp at b28 b29 b37 b38
  have bounds : ∀ i : Fin 6, (w ([45, 46, 47, 48, 51, 52].get i)).val < limbBase := by
    intro i
    have role := roles ⟨i.val, by have := i.isLt; omega⟩
    fin_cases operation <;> fin_cases i <;>
      dsimp [roleSources, Vector.get] at role ⊢ <;> rw [role]
    all_goals first | exact b28 | exact b29 | exact b37 | exact b38 |
      exact leftBound.1 | exact leftBound.2 | (simp [limbBase])
  have bytes := byte_values (by omega) h
  have q0 := bytes ⟨2, by decide⟩
  have q1 := bytes ⟨3, by decide⟩
  have d0 := bytes ⟨0, by decide⟩
  have d1 := bytes ⟨1, by decide⟩
  dsimp at q0 q1 d0 d1
  have dlo := roles ⟨6, by decide⟩
  have dhi := roles ⟨7, by decide⟩
  have dAlias : w 53 = w 24 ∧ w 54 = w 25 := by
    fin_cases operation <;> simpa [roleSources, Vector.get] using And.intro dlo dhi
  let q : Word := ⟨(w 49).val, (w 50).val⟩
  let d : Word := ⟨(w 24).val, (w 25).val⟩
  let r : Word := ⟨(w 51).val, (w 52).val⟩
  let low : Word := ⟨(w 45).val, (w 46).val⟩
  let high : Word := ⟨(w 47).val, (w 48).val⟩
  let carry (i : Fin 3) := (w (41 + i.val)).val
  apply product_of_columns (F := ZMod p) hp q d r low high carry
    ⟨q0.1, q1.1⟩ ⟨d0.1, d1.1⟩ ⟨bounds ⟨4, by decide⟩, bounds ⟨5, by decide⟩⟩
    ⟨bounds ⟨0, by decide⟩, bounds ⟨1, by decide⟩⟩
    ⟨bounds ⟨2, by decide⟩, bounds ⟨3, by decide⟩⟩ (carry_bounds h)
  intro i
  have e := Verification.assertion_of_holds h
    ⟨22 + i.val, by rw [constraint_count]; have := i.isLt; omega⟩
  have byte0 := Verification.assertion_of_holds h ⟨15, by rw [constraint_count]; decide⟩
  have byte1 := Verification.assertion_of_holds h ⟨16, by rw [constraint_count]; decide⟩
  have carry0 := Verification.assertion_of_holds h ⟨19, by rw [constraint_count]; decide⟩
  have carry1 := Verification.assertion_of_holds h ⟨20, by rw [constraint_count]; decide⟩
  have carry2 := Verification.assertion_of_holds h ⟨21, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at byte0 byte1 carry0 carry1 carry2
  have aliases : w 58 = w 33 ∧ w 59 = w 34 ∧ w 62 = w 41 ∧ w 63 = w 42 ∧ w 64 = w 43 := by
    repeat' apply And.intro
    all_goals first | (linear_combination byte0) | (linear_combination byte1) |
      (linear_combination carry0) | (linear_combination carry1) | (linear_combination carry2)
  have decompose (n : Nat) : (n : ZMod p) = (n % 256 : Nat) + 256 * ((n / 256 : Nat) : ZMod p) := by
    have eq := congrArg (fun n : Nat => (n : ZMod p)) (Nat.mod_add_div n 256)
    simpa using eq.symm
  have upper49 : w 49 - w 60 = 256 * (((w 49).val / 256 : Nat) : ZMod p) := by
    rw [q0.2]
    have eq := decompose (w 49).val
    simp only [ZMod.natCast_zmod_val] at eq
    linear_combination eq
  have upper50 : w 50 - w 61 = 256 * (((w 50).val / 256 : Nat) : ZMod p) := by
    rw [q1.2]
    have eq := decompose (w 50).val
    simp only [ZMod.natCast_zmod_val] at eq
    linear_combination eq
  have upper24 : w 24 - w 33 = 256 * (((w 24).val / 256 : Nat) : ZMod p) := by
    rw [d0.2]
    have eq := decompose (w 24).val
    simp only [ZMod.natCast_zmod_val] at eq
    linear_combination eq
  have upper25 : w 25 - w 34 = 256 * (((w 25).val / 256 : Nat) : ZMod p) := by
    rw [d1.2]
    have eq := decompose (w 25).val
    simp only [ZMod.natCast_zmod_val] at eq
    linear_combination eq
  have upper_product (a b : ZMod p) : (-30720 : ZMod p) * (256 * a) * (256 * b) = a * b := by
    calc
      _ = ((-30720 : ZMod p) * 65536) * (a * b) := by ring
      _ = a * b := by rw [inverse]; ring
  fin_cases i <;>
    simp [importedConstraints, FlatOperation.constraints,
      Expression.eval, Verification.environment] at e
  all_goals
    simp only [aliases.1, aliases.2.1, aliases.2.2.1, aliases.2.2.2.1, aliases.2.2.2.2,
      dAlias.1, dAlias.2, ← sub_eq_add_neg, upper49, upper50, upper24, upper25] at e
    simp only [sub_eq_add_neg, ← neg_mul, upper_product, q0.2, q1.2, d0.2, d1.2] at e
    dsimp [productColumns, productColumnOutputs, q, d, r, low, high, carry]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination e

end Airbender.MulDiv.Proofs
