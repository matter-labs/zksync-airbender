import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.UnifiedReduced.Setup
import Airbender.Proofs.ShiftBinop.Lookups

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem fixed_other_tags (i : Fin 1048961) (outside : ¬ i.val < 524545) :
    (fixedRow i)[9] = 1 ∨ (fixedRow i)[9] = 5 ∨ (fixedRow i)[9] = 2 ∨
      (fixedRow i)[9] = 51 ∨ (47 ≤ (fixedRow i)[9] ∧ (fixedRow i)[9] < 51) := by
  rw [fixedRow_eq_reference]
  unfold referenceFixedRow
  dsimp only
  split
  · contradiction
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inl rfl)
      · split
        · exact Or.inr (Or.inr (Or.inl rfl))
        · split
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
            change 47 ≤ 47 + (i.val - 786817) / 65536 ∧ 47 + (i.val - 786817) / 65536 < 51
            have size := i.isLt
            omega

theorem ordinary_region {before : Reference.RiscV.Sail.State} {i : Fin 2097537} {tag : Nat}
    (valid : tag = 3 ∨ tag = 8 ∨ tag = 9) (selected : (row before i)[9] = tag) :
    ∃ j : Fin 524545, row before i = shiftBinopRow j := by
  simp only [row_eq_reference] at *
  by_cases top : i.val < 1048961
  · by_cases first : i.val < 524545
    · have same : referenceRow before i = referenceBinaryRow ⟨i.val, first⟩ := by
        simp only [referenceRow, top, dif_pos, referenceFixedRow, first]
      have projected := congrArg (fun values : Vector Nat 10 => values[9]'(by decide)) same
      replace selected := projected.symm.trans selected
      have bound := shift_tag_bound ⟨i.val, first⟩
      have oldTag : (shiftBinopRow ⟨i.val, first⟩)[9] = tag := by
        simp only [referenceBinaryRow, Vector.getElem_set_self] at selected
        unfold binaryTag at selected
        rcases valid with rfl | rfl | rfl
        all_goals split_ifs at selected <;> omega
      refine ⟨⟨i.val, first⟩, same.trans ?_⟩
      apply Vector.ext
      intro k hk
      simp only [referenceBinaryRow, Vector.getElem_set]
      split
      · subst k
        simp only [oldTag]
        rcases valid with rfl | rfl | rfl <;> rfl
      · rfl
    · have same : referenceRow before i = referenceFixedRow ⟨i.val, top⟩ := dif_pos top
      have projected := congrArg (fun values : Vector Nat 10 => values[9]'(by decide)) same
      replace selected := projected.symm.trans selected
      have other := fixed_other_tags ⟨i.val, top⟩ first
      simp only [fixedRow_eq_reference] at other
      rcases valid with rfl | rfl | rfl <;> omega
  · have same : (referenceRow before i)[9] = 34 := by
      simp only [referenceRow, top]
      rfl
    rw [same] at selected
    rcases valid with rfl | rfl | rfl <;> omega

theorem ordinary_lookup [Fact p.Prime] (hp : FieldCapacity.AtLeast p 55)
    {before : Reference.RiscV.Sail.State} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)} (holds : (Lookup.mk (table before).toRaw entry).Contains env)
    (tag : Nat) (valid : tag = 3 ∨ tag = 8 ∨ tag = 9)
    (selected : entry[9].eval env = (tag : ZMod p)) :
    (shiftBinopLookup entry).Contains env := by
  obtain ⟨i, tagged, columns⟩ := lookup_row hp holds tag
    (by rcases valid with rfl | rfl | rfl <;> decide) selected
  obtain ⟨j, same⟩ := ordinary_region valid tagged
  change ∃ k : Fin 524545, entry.map (Expression.eval env) =
    (shiftBinopRow k).map (fun (n : Nat) => (n : ZMod p))
  refine ⟨j, ?_⟩
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_map]
  simpa only [same] using columns k hk

end Airbender.UnifiedReduced.Setup.Proofs
