import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.ArtifactChecks
import Airbender.Review.Circuits.UnifiedReduced.Artifact
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Arithmetic.Word
import Airbender.Proofs.Constraints
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace Airbender.UnifiedReduced.Proofs
open Airbender.Arithmetic

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

/-- The current native Boolean columns include the decoder flags, shared
scratch controls, PC carry and timestamp borrows. -/
theorem local_flags {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    ∀ i : Fin 30,
      w (#v[4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 52, 53, 54, 55, 56, 81, 122, 123, 124, 125][i]) = 0 ∨
      w (#v[4, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
        26, 27, 28, 29, 52, 53, 54, 55, 56, 81, 122, 123, 124, 125][i]) = 1 := by
  intro i
  have flag := Verification.assertion_of_holds h
    ⟨(#v[0, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104,
      105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119][i]),
      by rw [constraint_count]; fin_cases i <;> decide⟩
  fin_cases i <;> simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, mul_eq_zero, ← sub_eq_add_neg, sub_eq_zero, or_comm] at flag ⊢
  all_goals exact flag

open scoped BigOperators

/-- Active family dispatch has at most one selected sub-operation. The additional
    Family-2 rd-is-zero marker is excluded because it may accompany that operation. -/
theorem dispatch_count {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 18)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) :
    (∑ i : Fin 18, (w Variables.dispatchColumns[i]).val) ≤ 1 := by
  have definition := Verification.assertion_of_holds h ⟨87, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, active] at definition
  have bits : ∀ i : Fin 18, w Variables.dispatchColumns[i] = 0 ∨ w Variables.dispatchColumns[i] = 1 := by
    intro i
    have flag := local_flags h (#v[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19][i])
    fin_cases i <;> exact flag
  have total : (1 : ZMod p) = 0 ∨ (1 : ZMod p) = 1 := Or.inr rfl
  apply boolean_sum_le_one hp bits total
  simp [Variables.dispatchColumns, Fin.sum_univ_succ]
  linear_combination -definition

/-- A selected operation excludes every other dispatch bit on an active row. -/
theorem dispatch_exclusive {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 18)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (selected : Fin 18)
    (set : w Variables.dispatchColumns[selected] = 1) :
    ∀ i : Fin 18, i ≠ selected → w Variables.dispatchColumns[i] = 0 := by
  intro i different
  have total := dispatch_count hp h active
  have one : (w Variables.dispatchColumns[selected]).val = 1 := by
    rw [set]
    simpa only [Nat.cast_one] using ZMod.val_natCast_of_lt (n := p) (a := 1) (by omega)
  have zero := sum_le_one_exclusive total selected one i different
  have cast := ZMod.natCast_zmod_val (w Variables.dispatchColumns[i])
  rw [zero] at cast
  simpa only [Nat.cast_zero] using cast.symm

/-- Destination limbs are ranged independently of the selected family. -/
theorem destination_bounds {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 50).val < limbBase ∧ (w 51).val < limbBase := by
  have low := Verification.range16_bound (Verification.lookup_of_holds h ⟨2, by rw [lookup_count]; decide⟩)
  have high := Verification.range16_bound (Verification.lookup_of_holds h ⟨3, by rw [lookup_count]; decide⟩)
  simpa [Expression.eval, Verification.environment] using And.intro low high

/-- The initial high-PC limb is already ranged by the shared state interface. -/
theorem initial_pc_hi_bound {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 1).val < limbBase := by
  have bound := Verification.range16_bound (Verification.lookup_of_holds h ⟨4, by rw [lookup_count]; decide⟩)
  simpa [Expression.eval, Verification.environment] using bound

/-- Both final PC limbs are locally ranged, including Family-2 rows. -/
theorem pc_bounds {p : Nat} [Fact p.Prime] {setup : Table (ZMod p) (fields 10)}
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 30).val < limbBase ∧ (w 31).val < limbBase := by
  have low := Verification.range16_bound (Verification.lookup_of_holds h ⟨11, by rw [lookup_count]; decide⟩)
  have high := Verification.range16_bound (Verification.lookup_of_holds h ⟨12, by rw [lookup_count]; decide⟩)
  simpa [Expression.eval, Verification.environment] using And.intro low high

/-- Ordinary active rows use the shared PC increment. JAL/JALR/SLT/BRANCH use
    their own gated path; rd-is-zero is intentionally absent from this exclusion. -/
theorem pc_successor {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {initial final : Word}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (active : w 4 = 1) (outsideFamily2 : w 21 = 0 ∧ w 22 = 0 ∧ w 23 = 0 ∧ w 24 = 0)
    (mapping : w 0 = (initial.lo : ZMod p) ∧ w 1 = (initial.hi : ZMod p) ∧
      final.lo = (w 30).val ∧ final.hi = (w 31).val) (initialBound : initial.Bounded) :
    final.value = initial.value + 4 ∧ initial.value + 4 < wordModulus ∧
      final.toBitVec = initial.toBitVec + 4 := by
  have low := Verification.assertion_of_holds h ⟨85, by rw [constraint_count]; decide⟩
  have high := Verification.assertion_of_holds h ⟨86, by rw [constraint_count]; decide⟩
  have finalLo : w 30 = (final.lo : ZMod p) := by
    rw [mapping.2.2.1]; exact (ZMod.natCast_zmod_val _).symm
  have finalHi : w 31 = (final.hi : ZMod p) := by
    rw [mapping.2.2.2]; exact (ZMod.natCast_zmod_val _).symm
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, active, outsideFamily2.1, outsideFamily2.2.1,
    outsideFamily2.2.2.1, outsideFamily2.2.2.2, mapping.1, mapping.2.1, finalLo, finalHi] at low high
  have carry := boolean_val (local_flags h 26)
  have lowField : (initial.lo : ZMod p) + 4 = final.lo + 65536 * (w 122).val := by
    simp only [ZMod.natCast_zmod_val]
    linear_combination low
  have highField : (initial.hi : ZMod p) + (w 122).val = final.hi := by
    simp only [ZMod.natCast_zmod_val]
    linear_combination high
  have ranged := pc_bounds h
  have finalBound : final.Bounded := ⟨mapping.2.2.1 ▸ ranged.1, mapping.2.2.2 ▸ ranged.2⟩
  exact Word.increment_of_limbs hp (by decide) carry initialBound finalBound lowField highField

end Airbender.UnifiedReduced.Proofs
