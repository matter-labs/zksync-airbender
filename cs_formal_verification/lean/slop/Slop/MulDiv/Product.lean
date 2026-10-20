import Slop.MulDiv
import Slop.Arithmetic.Multiplication

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

/-- The division comparison equations force a strict remainder bound when the
    divisor is nonzero. Reuse the shared two-limb borrow theorem. -/
theorem remainder_lt_divisor {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (remainder : Bool)
    (selected : w 12 = (if remainder then 0 else 1) ∧ w 13 = (if remainder then 1 else 0))
    (other : w 10 = 0 ∧ w 11 = 0)
    (nonzero : (⟨(w 24).val, (w 25).val⟩ : Word).value ≠ 0) :
    (⟨(w 51).val, (w 52).val⟩ : Word).value <
      (⟨(w 24).val, (w 25).val⟩ : Word).value := by
  let operation : Fin 4 := if remainder then 3 else 2
  have selection : ∀ i : Fin 4, w (10 + i.val) = if i = operation then 1 else 0 := by
    intro i
    cases remainder <;> fin_cases i <;> simpa [operation] using
      (by first | exact other.1 | exact other.2 | exact selected.1 | exact selected.2)
  have roles := product_wiring h operation selection
  have ranges := local_ranges h
  have b28 := ranges ⟨0, by decide⟩
  have b29 := ranges ⟨1, by decide⟩
  have b37 := ranges ⟨2, by decide⟩
  have b38 := ranges ⟨3, by decide⟩
  have rlo := roles ⟨4, by decide⟩
  have rhi := roles ⟨5, by decide⟩
  have rb : (⟨(w 51).val, (w 52).val⟩ : Word).Bounded := by
    cases remainder <;> dsimp [operation, roleSources, Vector.get] at rlo rhi <;>
      rw [rlo, rhi] <;> first | exact ⟨b37, b38⟩ | exact ⟨b28, b29⟩
  have dlo := roles ⟨6, by decide⟩
  have dhi := roles ⟨7, by decide⟩
  have dAlias : w 53 = w 24 ∧ w 54 = w 25 := by
    cases remainder <;> simpa [operation, roleSources, Vector.get] using And.intro dlo dhi
  have fixed := Verification.regIsZero_value (by omega : 131072 ≤ p)
    (Verification.lookup_of_holds h ⟨8, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at fixed
  have zeroFlag : w 32 = 0 := by
    have boolean : w 32 = 0 ∨ w 32 = 1 := by rw [fixed.2]; split_ifs <;> simp
    rcases boolean with zero | one
    · exact zero
    · exact False.elim (nonzero ((divisor_zero_iff (by omega) h).mp one))
  have z := Verification.assertion_of_holds h ⟨1, by rw [constraint_count]; decide⟩
  have div := Verification.assertion_of_holds h ⟨12, by rw [constraint_count]; decide⟩
  have cmpLo := Verification.assertion_of_holds h ⟨13, by rw [constraint_count]; decide⟩
  have cmpHi := Verification.assertion_of_holds h ⟨14, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨26, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨27, by rw [constraint_count]; decide⟩
  have divisionFlags : w 44 = 0 ∧ w 55 = 1 := by
    cases remainder <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected.1, selected.2, zeroFlag] at z div
    all_goals constructor
    all_goals first | exact z | (linear_combination div)
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment] at cmpLo cmpHi
  have cmpAlias : w 56 = w 39 ∧ w 57 = w 40 := by
    constructor
    · linear_combination cmpLo
    · linear_combination cmpHi
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, cmpAlias.1, cmpAlias.2, dAlias.1, dAlias.2,
    divisionFlags.1, divisionFlags.2, -mul_eq_zero] at low high
  let b : ZMod p := -30720 * (w 39 + w 24 - w 51)
  have boolean : b * (b - 1) = 0 := by
    dsimp [b]
    linear_combination -low
  have normalized : b + (w 25 + w 40) - (65536 + w 52) = 0 := by
    dsimp [b]
    linear_combination -high
  obtain ⟨c, cb, lo, hi⟩ := increment_carry inverse boolean normalized
  have bytes := byte_values (by omega) h
  apply (Word.borrow_iff (left := ⟨(w 51).val, (w 52).val⟩)
    (right := ⟨(w 24).val, (w 25).val⟩) (remainder := ⟨(w 39).val, (w 40).val⟩)
    hp rb ⟨(bytes ⟨0, by decide⟩).1, (bytes ⟨1, by decide⟩).1⟩
    ⟨ranges ⟨4, by decide⟩, ranges ⟨5, by decide⟩⟩ cb (by decide : 1 ≤ 1) ?_ ?_).mp rfl
  · simpa [ZMod.natCast_zmod_val] using lo
  · simpa [ZMod.natCast_zmod_val, add_assoc, add_comm, add_left_comm] using hi

/-- Nonzero unsigned division is uniquely fixed by the exact product relation
    and strict remainder bound, using Lean's natural division uniqueness theorem. -/
theorem division_nonzero {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (remainder : Bool)
    (selected : w 12 = (if remainder then 0 else 1) ∧ w 13 = (if remainder then 1 else 0))
    (other : w 10 = 0 ∧ w 11 = 0)
    (leftBound : (w 20).val < limbBase ∧ (w 21).val < limbBase)
    (nonzero : (⟨(w 24).val, (w 25).val⟩ : Word).value ≠ 0) :
    (⟨(w 28).val, (w 29).val⟩ : Word).value =
      if remainder then (⟨(w 20).val, (w 21).val⟩ : Word).value %
          (⟨(w 24).val, (w 25).val⟩ : Word).value
      else (⟨(w 20).val, (w 21).val⟩ : Word).value /
          (⟨(w 24).val, (w 25).val⟩ : Word).value := by
  let operation : Fin 4 := if remainder then 3 else 2
  have selection : ∀ i : Fin 4, w (10 + i.val) = if i = operation then 1 else 0 := by
    intro i
    cases remainder <;> fin_cases i <;> simpa [operation] using
      (by first | exact other.1 | exact other.2 | exact selected.1 | exact selected.2)
  have product := product_with_remainder hp inverse h operation selection leftBound
  have roles := product_wiring h operation selection
  have low0 := roles ⟨0, by decide⟩
  have low1 := roles ⟨1, by decide⟩
  have high0 := roles ⟨2, by decide⟩
  have high1 := roles ⟨3, by decide⟩
  have dividend : (⟨(w 49).val, (w 50).val⟩ : Word).value *
      (⟨(w 24).val, (w 25).val⟩ : Word).value +
      (⟨(w 51).val, (w 52).val⟩ : Word).value =
      (⟨(w 20).val, (w 21).val⟩ : Word).value := by
    cases remainder <;> dsimp [operation, roleSources, Vector.get] at low0 low1 high0 high1 <;>
      simpa [low0, low1, high0, high1, Word.value] using product
  have lt := remainder_lt_divisor (by omega) inverse h remainder selected other nonzero
  have unique := (Nat.div_mod_unique
    (a := (⟨(w 20).val, (w 21).val⟩ : Word).value)
    (d := (⟨(w 49).val, (w 50).val⟩ : Word).value)
    (c := (⟨(w 51).val, (w 52).val⟩ : Word).value)
    (Nat.pos_of_ne_zero nonzero)).mpr
    ⟨by simpa [mul_comm, add_comm] using dividend, lt⟩
  have qlo := Verification.assertion_of_holds h ⟨6, by rw [constraint_count]; decide⟩
  have qhi := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  have rlo := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  have rhi := Verification.assertion_of_holds h ⟨9, by rw [constraint_count]; decide⟩
  cases remainder <;>
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, selected.1, selected.2, other.1, other.2] at qlo qhi rlo rhi
  · have lo : w 49 = w 28 := by linear_combination qlo
    have hi : w 50 = w 29 := by linear_combination qhi
    simpa [lo, hi] using unique.1.symm
  · have lo : w 51 = w 28 := by linear_combination rlo
    have hi : w 52 = w 29 := by linear_combination rhi
    simpa [lo, hi] using unique.2.symm

/-- MUL/MULHU select the low/high half of the exact product. The low half's
    range makes this decomposition unique, without assuming the output. -/
theorem multiplication_result {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (high : Bool)
    (selected : ∀ i : Fin 4, w (10 + i.val) = if i = (if high then 1 else 0) then 1 else 0)
    (leftBound : (w 20).val < limbBase ∧ (w 21).val < limbBase) :
    (⟨(w 28).val, (w 29).val⟩ : Word).value =
      if high then ((⟨(w 20).val, (w 21).val⟩ : Word).value *
        (⟨(w 24).val, (w 25).val⟩ : Word).value) / wordModulus
      else ((⟨(w 20).val, (w 21).val⟩ : Word).value *
        (⟨(w 24).val, (w 25).val⟩ : Word).value) % wordModulus := by
  let operation : Fin 4 := if high then 1 else 0
  have product := product_with_remainder hp inverse h operation selected leftBound
  have roles := product_wiring h operation selected
  have s0 := selected ⟨0, by decide⟩
  have s1 := selected ⟨1, by decide⟩
  have s2 := selected ⟨2, by decide⟩
  have s3 := selected ⟨3, by decide⟩
  have qlo := Verification.assertion_of_holds h ⟨6, by rw [constraint_count]; decide⟩
  have qhi := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  have quotient : w 49 = w 20 ∧ w 50 = w 21 := by
    cases high <;>
      simp [importedConstraints, FlatOperation.constraints, Expression.eval,
        Verification.environment] at s0 s1 s2 s3 qlo qhi <;>
      simp [s0, s1, s2, s3] at qlo qhi <;> constructor
    all_goals first | linear_combination qlo | linear_combination qhi
  have rlo := roles ⟨4, by decide⟩
  have rhi := roles ⟨5, by decide⟩
  have exactProduct : (⟨(w 20).val, (w 21).val⟩ : Word).value *
      (⟨(w 24).val, (w 25).val⟩ : Word).value =
      (⟨(w 45).val, (w 46).val⟩ : Word).value + wordModulus *
      (⟨(w 47).val, (w 48).val⟩ : Word).value := by
    cases high <;> dsimp [operation, roleSources, Vector.get] at rlo rhi <;>
      simpa [quotient.1, quotient.2, rlo, rhi, Word.value] using product
  have lo := roles ⟨0, by decide⟩
  have hi := roles ⟨1, by decide⟩
  have ranges := local_ranges h
  have lowBound : (⟨(w 45).val, (w 46).val⟩ : Word).Bounded := by
    cases high <;> dsimp [operation, roleSources, Vector.get] at lo hi <;>
      simp only [Word.Bounded, lo, hi]
    · exact ⟨ranges ⟨0, by decide⟩, ranges ⟨1, by decide⟩⟩
    · exact ⟨ranges ⟨2, by decide⟩, ranges ⟨3, by decide⟩⟩
  have unique := (Nat.div_mod_unique
    (a := (⟨(w 20).val, (w 21).val⟩ : Word).value *
      (⟨(w 24).val, (w 25).val⟩ : Word).value)
    (b := wordModulus) (d := (⟨(w 47).val, (w 48).val⟩ : Word).value)
    (c := (⟨(w 45).val, (w 46).val⟩ : Word).value) (by decide)).mpr
    ⟨by simpa [add_comm] using exactProduct.symm, Word.value_lt lowBound⟩
  have upperLo := roles ⟨2, by decide⟩
  have upperHi := roles ⟨3, by decide⟩
  cases high <;> dsimp [operation, roleSources, Vector.get] at lo hi upperLo upperHi
  · simpa [lo, hi] using unique.2.symm
  · simpa [upperLo, upperHi] using unique.1.symm

end Airbender.MulDiv.Proofs
