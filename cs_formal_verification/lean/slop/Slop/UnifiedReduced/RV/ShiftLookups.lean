import Slop.UnifiedReduced.RV.Setup
import Slop.ShiftBinop.Lookups

namespace Airbender.UnifiedReduced.Setup.Proofs.RV
open Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem fixed_other_tags (i : Fin 1048961) (outside : ¬ i.val < 524545) :
    (fixedRow i)[9] = 1 ∨ (fixedRow i)[9] = 5 ∨ (fixedRow i)[9] = 2 ∨
      (fixedRow i)[9] = 51 ∨ (47 ≤ (fixedRow i)[9] ∧ (fixedRow i)[9] < 51) := by
  unfold fixedRow
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

theorem ordinary_region {words : Nat → BitVec 32} {i : Fin 2097537} {tag : Nat}
    (valid : tag = 3 ∨ tag = 8 ∨ tag = 9) (selected : (rowWith words i)[9] = tag) :
    ∃ j : Fin 524545, rowWith words i = shiftBinopRow j := by
  by_cases top : i.val < 1048961
  · by_cases first : i.val < 524545
    · have same : rowWith words i = binaryRow ⟨i.val, first⟩ := by
        simp only [rowWith, top, dite_eq_left, fixedRow, first]
      rw [same] at selected
      have bound := shift_tag_bound ⟨i.val, first⟩
      have oldTag : (shiftBinopRow ⟨i.val, first⟩)[9] = tag := by
        simp only [binaryRow, Vector.getElem_set_self] at selected
        unfold binaryTag at selected
        rcases valid with rfl | rfl | rfl
        all_goals split_ifs at selected <;> omega
      refine ⟨⟨i.val, first⟩, same.trans ?_⟩
      apply Vector.ext
      intro k hk
      simp only [binaryRow, Vector.getElem_set]
      split
      · subst k
        simp only [oldTag]
        rcases valid with rfl | rfl | rfl <;> rfl
      · rfl
    · have same : rowWith words i = fixedRow ⟨i.val, top⟩ := dite_eq_left top
      rw [same] at selected
      have other := fixed_other_tags ⟨i.val, top⟩ first
      rcases valid with rfl | rfl | rfl <;> omega
  · have same : (rowWith words i)[9] = 34 := by
      simp only [rowWith, top]
      rfl
    rw [same] at selected
    rcases valid with rfl | rfl | rfl <;> omega

theorem ordinary_lookup [Fact p.Prime] (hp : 55 ≤ p)
    {words : Nat → BitVec 32} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)} (holds : (Lookup.mk (tableWith words).toRaw entry).Contains env)
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

end Airbender.UnifiedReduced.Setup.Proofs.RV
