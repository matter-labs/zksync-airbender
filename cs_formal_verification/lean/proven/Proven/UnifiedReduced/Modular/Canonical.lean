module
public import Proven.UnifiedReduced
public import Proven.Arithmetic.Lemmas
public import Human.Circuits.AddSub.Modular.Model

@[expose] public section
namespace Airbender.UnifiedReduced.Modular.Proofs
open Arithmetic
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Name the standalone calculation's variables with the actual unified columns. -/
def lift (w : Nat → ZMod babyBearModulus) : Nat → ZMod babyBearModulus
  | 10 => w 11 | 11 => w 12 | 12 => w 13 | 13 => w 14 | 14 => w 15
  | 15 => w 16 | 16 => w 17 | 17 => w 18 | 18 => w 19
  | 19 => w 30 | 20 => w 31 | 21 => w 32 | 22 => w 33
  | 23 => w 34 | 24 => w 35 | 25 => w 36 | 26 => w 37
  | 27 => w 40 | 28 => w 41 | 29 => w 42 | 30 => w 43
  | 31 => w 48 | 32 => w 49 | 33 => w 50 | 34 => w 51
  | 35 => w 46 | 36 => w 47 | 37 => w 74 | 38 => w 75
  | 39 => w 53 | 40 => w 52 | 41 => w 78
  | 42 => w 123 | 43 => w 124 | 44 => w 125
  | i => w i

theorem canonical_output {setup : Table (ZMod babyBearModulus) (fields 10)}
    {w : Nat → ZMod babyBearModulus}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (s11 : w 11 = 0) (s12 : w 12 = 0) (s13 : w 13 = 0) (s20 : w 20 = 0)
    (selected : w 14 + w 15 + w 16 + w 17 = 1) :
    (w 50).val + 65536 * (w 51).val < babyBearModulus := by
  have borrow := Verification.assertion_of_holds h ⟨3, by rw [UnifiedReduced.constraint_count]; decide⟩
  have low := Verification.assertion_of_holds h ⟨4, by rw [UnifiedReduced.constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨5, by rw [UnifiedReduced.constraint_count]; decide⟩
  op_index at borrow low high
  simp [Expression.eval,
    Verification.environment, s11, s12, s13, s20, selected] at borrow low high
  have b : w 52 = 1 := by linear_combination -borrow
  have boolean : w 53 * (w 53 - 1) = 0 := by
    rcases UnifiedReduced.Proofs.local_flags h 21 with zero | one
    · simp only [show w 53 = 0 from zero, zero_mul]
    · simp only [show w 53 = 1 from one, sub_self, mul_zero]
  obtain ⟨c, cb, hc⟩ := boolean_nat boolean
  have rlo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨0, by rw [UnifiedReduced.lookup_count]; decide⟩)
  have rhi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨1, by rw [UnifiedReduced.lookup_count]; decide⟩)
  have olo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨2, by rw [UnifiedReduced.lookup_count]; decide⟩)
  have ohi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨3, by rw [UnifiedReduced.lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at rlo rhi olo ohi
  have lowEq : (((w 74).val : Nat) : ZMod babyBearModulus) + 1 =
      (w 50).val + 65536 * c := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc] at low
    linear_combination low
  have highEq : (c : ZMod babyBearModulus) + (w 75).val + 30720 = (w 51).val + 65536 := by
    simp only [ZMod.natCast_zmod_val]
    rw [hc, b] at high
    linear_combination high
  exact (Word.borrow_iff (p := babyBearModulus) (left := ⟨(w 50).val, (w 51).val⟩)
    (right := ⟨1, 30720⟩) (remainder := ⟨(w 74).val, (w 75).val⟩)
    (by decide) ⟨olo, ohi⟩ ⟨by decide, by decide⟩ ⟨rlo, rhi⟩ cb (borrow := 1) (by decide)
    (by simpa using lowEq) (by simpa using highEq)).mp rfl

end Airbender.UnifiedReduced.Modular.Proofs
