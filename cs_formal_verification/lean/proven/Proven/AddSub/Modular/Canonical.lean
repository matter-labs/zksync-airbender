module
public import Human.Circuits.AddSub.Modular.Model
public import Proven.AddSub.ArtifactChecks
public import Proven.AddSub.OpIndex
public import Proven.Arithmetic.Word
public import Proven.Arithmetic.Lemmas
public import Proven.Constraints
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Airbender.AddSub.Proofs
open Airbender.Arithmetic

theorem modular_canonical_output {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (s10 : w 10 = 0) (s11 : w 11 = 0) (s12 : w 12 = 0)
    (selected : w 13 + w 14 + w 15 + w 16 = 1) :
    (w 33).val + 65536 * (w 34).val < babyBearModulus := by
  have borrow := Verification.assertion_of_holds h
    ⟨3, by rw [constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h
    ⟨4, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h
    ⟨5, by rw [constraint_count]; decide⟩
  have carry := Verification.assertion_of_holds h
    ⟨25, by rw [constraint_count]; decide⟩
  op_index at borrow low high carry
  simp [Expression.eval,
    Verification.environment, s10, s11, s12, selected] at borrow low high carry
  have b : w 40 = 1 := by linear_combination -borrow
  have boolean : w 39 * (w 39 - 1) = 0 := by
    simpa [mul_eq_zero, sub_eq_add_neg] using carry
  obtain ⟨c, cb, hc⟩ := boolean_nat boolean
  have rlo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨0, by rw [lookup_count]; decide⟩)
  have rhi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨1, by rw [lookup_count]; decide⟩)
  have olo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨2, by rw [lookup_count]; decide⟩)
  have ohi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨3, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at rlo rhi olo ohi
  have lowEq : (((w 37).val : Nat) : ZMod p) + 1 =
      (w 33).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc] at low
    linear_combination low
  have highEq : (c : ZMod p) + (w 38).val + 30720 = (w 34).val + 65536 := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc, b] at high
    linear_combination high
  exact (Word.borrow_iff (left := ⟨(w 33).val, (w 34).val⟩)
    (right := ⟨1, 30720⟩) (remainder := ⟨(w 37).val, (w 38).val⟩)
    hp ⟨olo, ohi⟩ ⟨by decide, by decide⟩ ⟨rlo, rhi⟩ cb (borrow := 1) (by decide)
    (by simpa using lowEq) (by simpa using highEq)).mp rfl

end Airbender.AddSub.Proofs
