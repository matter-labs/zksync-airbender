import Slop.UnifiedReduced.ShiftLookups
import Slop.Lookups

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private def controlOffset (tag : Nat) : Nat :=
  if tag = 1 then 524545 else if tag = 5 then 655617 else if tag = 2 then 721153 else 786689
private def controlSize (tag : Nat) : Nat :=
  if tag = 1 then 131072 else if tag = 51 then 128 else 65536

private theorem binary_tags (i : Fin 524545) :
    (binaryRow i)[9] = 0 ∨ (binaryRow i)[9] = 3 ∨ (binaryRow i)[9] = 8 ∨
      (binaryRow i)[9] = 9 ∨ 52 ≤ (binaryRow i)[9] := by
  simp only [binaryRow, Vector.getElem_set_self]
  unfold shiftBinopRow
  dsimp only
  split_ifs <;> simp [binaryByteRow, binaryTag]

private theorem control_location {before : Reference.RiscV.Sail.State} {i : Fin 2097537} {tag : Nat}
    (valid : tag = 1 ∨ tag = 5 ∨ tag = 2 ∨ tag = 51) (selected : (row before i)[9] = tag) :
    controlOffset tag ≤ i.val ∧ i.val < controlOffset tag + controlSize tag := by
  by_cases top : i.val < 1048961
  · have same : row before i = fixedRow ⟨i.val, top⟩ := dif_pos top
    rw [same] at selected
    by_cases first : i.val < 524545
    · have same : fixedRow ⟨i.val, top⟩ = binaryRow ⟨i.val, first⟩ := by
        simp only [fixedRow, first, dif_pos]
      rw [same] at selected
      have tags := binary_tags ⟨i.val, first⟩
      rcases valid with rfl | rfl | rfl | rfl <;> omega
    · unfold fixedRow at selected
      dsimp only at selected
      split at selected
      · contradiction
      · split at selected
        · change 1 = tag at selected
          rcases valid with rfl | rfl | rfl | rfl
          all_goals simp [controlOffset, controlSize]; omega
        · split at selected
          · change 5 = tag at selected
            rcases valid with rfl | rfl | rfl | rfl
            all_goals simp [controlOffset, controlSize]; omega
          · split at selected
            · change 2 = tag at selected
              rcases valid with rfl | rfl | rfl | rfl
              all_goals simp [controlOffset, controlSize]; omega
            · split at selected
              · change 51 = tag at selected
                rcases valid with rfl | rfl | rfl | rfl
                all_goals simp [controlOffset, controlSize]; omega
              · change 47 + (i.val - 786817) / 65536 = tag at selected
                have bound := i.isLt
                rcases valid with rfl | rfl | rfl | rfl <;> omega
  · have tagValue : (row before i)[9] = 34 := by simp only [row, top]; rfl
    rw [tagValue] at selected
    rcases valid with rfl | rfl | rfl | rfl <;> omega

theorem control_region {before : Reference.RiscV.Sail.State} {i : Fin 2097537} {tag : Nat}
    (valid : tag = 1 ∨ tag = 5 ∨ tag = 2 ∨ tag = 51) (selected : (row before i)[9] = tag) :
    ∃ key : Nat, key < (if tag = 1 then 131072 else if tag = 51 then 128 else 65536) ∧
      row before i = if tag = 1 then #v[key, if key = 0 then 1 else 0, 0, 0, 0, 0, 0, 0, 0, 1]
      else if tag = 5 then #v[key, key / 32768, 0, 0, 0, 0, 0, 0, 0, 5]
      else if tag = 2 then #v[key, key / 2 % 2, key - key % 4, 0, 0, 0, 0, 0, 0, 2]
      else #v[key, conditionalValue (conditionalKey key), 0, 0, 0, 0, 0, 0, 0, 51] := by
  have location := control_location valid selected
  refine ⟨i.val - controlOffset tag, ?_, ?_⟩
  · change i.val - controlOffset tag < controlSize tag
    omega
  · rcases valid with rfl | rfl | rfl | rfl
    all_goals simp [controlOffset, controlSize] at location
    all_goals simp [row, fixedRow, controlOffset,
      show i.val < 1048961 by omega,
      show ¬i.val < 524545 by omega]
    all_goals split_ifs <;> simp_all <;> omega

theorem zero_lookup [Fact p.Prime] (hp : 55 ≤ p)
    {before : Reference.RiscV.Sail.State} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)} (holds : (Lookup.mk (table before).toRaw entry).Contains env)
    (selected : entry[9].eval env = 1) :
    (pairLookup regIsZeroTable entry[0] entry[1]).Contains env := by
  obtain ⟨i, tag, columns⟩ := lookup_row hp holds 1 (by decide) (by simpa using selected)
  obtain ⟨key, bound, layout⟩ := control_region (Or.inl rfl) tag
  apply (pairLookup regIsZeroTable entry[0] entry[1]).table.implied_by_completeness
  apply (Lookup.completeness_def regIsZeroTable env (entry[0], entry[1])).mpr
  with_unfolding_all change ∃ j : Fin 131072, (entry[0].eval env, entry[1].eval env) =
    ((j.val : ZMod p), ((if j.val = 0 then 1 else 0 : Nat) : ZMod p))
  refine ⟨⟨key, by simpa using bound⟩, ?_⟩
  apply Prod.ext
  · simpa [layout] using columns 0 (by decide)
  · simpa [layout] using columns 1 (by decide)

theorem sign_lookup [Fact p.Prime] (hp : 55 ≤ p)
    {before : Reference.RiscV.Sail.State} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)} (holds : (Lookup.mk (table before).toRaw entry).Contains env)
    (selected : entry[9].eval env = 5) :
    (pairLookup u16SignTable entry[0] entry[1]).Contains env := by
  obtain ⟨i, tag, columns⟩ := lookup_row hp holds 5 (by decide) (by simpa using selected)
  obtain ⟨key, bound, layout⟩ := control_region (Or.inr (Or.inl rfl)) tag
  apply (pairLookup u16SignTable entry[0] entry[1]).table.implied_by_completeness
  apply (Lookup.completeness_def u16SignTable env (entry[0], entry[1])).mpr
  with_unfolding_all change ∃ j : Fin 65536, (entry[0].eval env, entry[1].eval env) =
    ((j.val : ZMod p), ((j.val / 32768 : Nat) : ZMod p))
  refine ⟨⟨key, by simpa using bound⟩, ?_⟩
  apply Prod.ext
  · simpa [layout] using columns 0 (by decide)
  · simpa [layout] using columns 1 (by decide)

theorem cleanup_lookup [Fact p.Prime] (hp : 55 ≤ p)
    {before : Reference.RiscV.Sail.State} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)} (holds : (Lookup.mk (table before).toRaw entry).Contains env)
    (selected : entry[9].eval env = 2) :
    (jumpCleanup entry[0] entry[1] entry[2]).Contains env := by
  obtain ⟨i, tag, columns⟩ := lookup_row hp holds 2 (by decide) (by simpa using selected)
  obtain ⟨key, bound, layout⟩ := control_region (Or.inr (Or.inr (Or.inl rfl))) tag
  apply (jumpCleanup entry[0] entry[1] entry[2]).table.implied_by_completeness
  apply (Lookup.completeness_def jumpCleanupTable env (entry[0], entry[1], entry[2])).mpr
  with_unfolding_all change ∃ j : Fin 65536, (entry[0].eval env, entry[1].eval env, entry[2].eval env) =
    ((j.val : ZMod p), ((j.val / 2 % 2 : Nat) : ZMod p), ((j.val - j.val % 4 : Nat) : ZMod p))
  refine ⟨⟨key, by simpa using bound⟩, ?_⟩
  apply Prod.ext
  · simpa [layout] using columns 0 (by decide)
  · apply Prod.ext
    · simpa [layout] using columns 1 (by decide)
    · simpa [layout] using columns 2 (by decide)

theorem conditional_lookup [Fact p.Prime] (hp : 128 ≤ p)
    {before : Reference.RiscV.Sail.State} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)} (holds : (Lookup.mk (table before).toRaw entry).Contains env)
    (selected : entry[9].eval env = 51) :
    (entry[0].eval env).val < 128 ∧ entry[1].eval env =
      (conditionalValue (conditionalKey (entry[0].eval env).val) : ZMod p) := by
  obtain ⟨i, tag, columns⟩ := lookup_row (by omega) holds 51 (by decide) (by simpa using selected)
  obtain ⟨key, bound, layout⟩ := control_region (Or.inr (Or.inr (Or.inr rfl))) tag
  apply pair_value_of_row (value := fun key => conditionalValue (conditionalKey key)) hp
  refine ⟨⟨key, by simpa using bound⟩, ?_⟩
  apply Prod.ext
  · simpa [layout] using columns 0 (by decide)
  · simpa [layout] using columns 1 (by decide)

end Airbender.UnifiedReduced.Setup.Proofs
