module
public import Slop.AddSub.RowModel
public import Slop.AddSub.OpIndex
public import Slop.Arithmetic.Lemmas
public import Slop.Arithmetic.Word
public import Slop.Constraints
public import Mathlib.Tactic.LinearCombination
public import Human.Helpers.Properties
public import Slop.AddSub.ArtifactChecks
public import Slop.CleanCore.Circuit.Operations
public import Slop.Defs.Circuits.AddSub.Artifact
public import Slop.Defs.Helpers.Core.Word

@[expose] public section

namespace Airbender.AddSub.Proofs
open Airbender.Arithmetic

/-- Final PC bounds come from the last two imported range queries. -/
theorem pc_bounds {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : PCMapping initial final w) : final.Bounded := by
  have lo := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨4, by rw [lookup_count]; decide⟩)
  have hi := Verification.range16_bound (Verification.lookup_of_holds h
    ⟨5, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment] at lo hi
  exact ⟨mapping.finalLo ▸ lo, mapping.finalHi ▸ hi⟩

private theorem pc_equations {p : Nat} [Fact p.Prime]
    (inverse : (-30720 : ZMod p) * 65536 = 1) {w : Nat → ZMod p}
    {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : PCMapping initial final w) :
    ∃ c : Nat, c ≤ 1 ∧
      (initial.lo : ZMod p) + 4 = final.lo + 65536 * c ∧
      (initial.hi : ZMod p) + c = final.hi := by
  have carry := Verification.assertion_of_holds h
    ⟨12, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h
    ⟨13, by rw [constraint_count]; decide⟩
  have finalLo : w 19 = (final.lo : ZMod p) := by
    rw [mapping.finalLo]; exact (ZMod.natCast_zmod_val _).symm
  have finalHi : w 20 = (final.hi : ZMod p) := by
    rw [mapping.finalHi]; exact (ZMod.natCast_zmod_val _).symm
  op_index at carry high
  simp [Expression.eval, Verification.environment, mapping.initialLo, mapping.initialHi, finalLo, finalHi] at carry high
  let expression : ZMod p := -30720 * (initial.lo + 4 - final.lo)
  have boolean : expression * (expression - 1) = 0 := by
    simpa [expression, mul_eq_zero, sub_eq_add_neg] using carry
  have normalized : expression + initial.hi - final.hi = 0 := by
    convert high using 1
    dsimp [expression]
    ring
  exact Arithmetic.increment_carry inverse boolean normalized

/-- The imported equations increment PC by four without high-word overflow.
    The inverse premise refers to the serialized BabyBear constant, not a replacement
    inverse for another field. No execution-selector or honest-witness assumption is used. -/
theorem pc_successor {p : Nat} [Fact p.Prime]
    (hp : 196608 < p) (inverse : (-30720 : ZMod p) * 65536 = 1)
    {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints)
    (mapping : PCMapping initial final w) (initialBounds : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 := by
  obtain ⟨c, cb, lo, hi⟩ := pc_equations inverse h mapping
  exact Word.increment_of_limbs (by omega) (by decide) cb initialBounds
    (pc_bounds h mapping) lo hi

end Airbender.AddSub.Proofs
