import Airbender.Proofs.UnifiedReduced.Tables.FixedCharacterization
import Airbender.Proofs.Tables.ShiftCharacterization
import Airbender.Review.Circuits.UnifiedReduced.Tables.Setup
import Airbender.Proofs.ByteTables

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem shift_tag_bound (i : Fin 524545) : (shiftBinopRow i)[9] < 10 := by
  simp only [shiftBinopRow_eq_reference]
  unfold referenceShiftBinopRow referenceShiftNatRow
  dsimp only
  split_ifs <;> simp [binaryByteRow]

theorem row_tag_bound (before : Reference.RiscV.Sail.State) (i : Fin 2097537) :
    (row before i)[9] < 55 := by
  rw [row_eq_reference]
  unfold referenceRow
  split
  · unfold referenceFixedRow
    dsimp only
    split
    · have bound := shift_tag_bound ⟨i.val, by assumption⟩
      simp only [referenceBinaryRow, Vector.getElem_set_self]
      unfold binaryTag
      split_ifs <;> omega
    · split
      · change 1 < 55; decide
      · split
        · change 5 < 55; decide
        · split
          · change 2 < 55; decide
          · split
            · change 51 < 55; decide
            · change 47 + (i.val - 786817) / 65536 < 55
              have bound := i.isLt
              omega
  · change 34 < 55; decide

theorem lookup_row [Fact p.Prime] (hp : 55 ≤ p)
    {before : Reference.RiscV.Sail.State} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)} (holds : (Lookup.mk (table before).toRaw entry).Contains env)
    (tag : Nat) (small : tag < 55) (selected : entry[9].eval env = (tag : ZMod p)) :
    ∃ i : Fin 2097537, (row before i)[9] = tag ∧
      ∀ j : Nat, ∀ hj : j < 10, entry[j].eval env = ((row before i)[j] : ZMod p) := by
  change ∃ i : Fin 2097537, entry.map (Expression.eval env) =
    (row before i).map (fun (n : Nat) => (n : ZMod p)) at holds
  obtain ⟨i, rows⟩ := holds
  have column (j : Nat) (hj : j < 10) :
      entry[j].eval env = ((row before i)[j] : ZMod p) := by
    have equal := congrArg (fun (v : Vector (ZMod p) 10) => v[j]) rows
    simpa only [Vector.getElem_map] using equal
  refine ⟨i, ?_, column⟩
  have equal := congrArg ZMod.val ((column 9 (by decide)).symm.trans selected)
  have bound := row_tag_bound before i
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : (row before i)[9] < p),
    Nat.mod_eq_of_lt (by omega : tag < p)] using equal

theorem fixed_outside_tag (i : Fin 1048961) (outside : ¬ i.val < 524545) :
    (fixedRow i)[9] < 52 := by
  rw [fixedRow_eq_reference]
  unfold referenceFixedRow
  dsimp only
  split
  · contradiction
  · split
    · change 1 < 52; decide
    · split
      · change 5 < 52; decide
      · split
        · change 2 < 52; decide
        · split
          · change 51 < 52; decide
          · change 47 + (i.val - 786817) / 65536 < 52
            have bound := i.isLt
            omega

theorem wide_region {before : Reference.RiscV.Sail.State} {i : Fin 2097537} {tag : Nat}
    (wide : tag = 4 ∨ tag = 6 ∨ tag = 7) (selected : (row before i)[9] = binaryTag tag) :
    ∃ j : Fin 524545, row before i = binaryRow j ∧ (shiftBinopRow j)[9] = tag := by
  simp only [row_eq_reference, binaryRow_eq_reference] at *
  have ht : binaryTag tag = 52 ∨ binaryTag tag = 53 ∨ binaryTag tag = 54 := by
    rcases wide with rfl | rfl | rfl <;> simp [binaryTag]
  by_cases top : i.val < 1048961
  · by_cases first : i.val < 524545
    · have same : referenceRow before i = referenceBinaryRow ⟨i.val, first⟩ := by
        simp only [referenceRow, top, dif_pos, referenceFixedRow, first]
      refine ⟨⟨i.val, first⟩, same, ?_⟩
      have projected := congrArg (fun values : Vector Nat 10 => values[9]'(by decide)) same
      replace selected : (referenceBinaryRow ⟨i.val, first⟩)[9] = binaryTag tag :=
        projected.symm.trans selected
      have bound := shift_tag_bound ⟨i.val, first⟩
      simp only [referenceBinaryRow, Vector.getElem_set_self] at selected
      unfold binaryTag at selected
      rcases wide with rfl | rfl | rfl
      all_goals split_ifs at selected <;> omega
    · have same : referenceRow before i = referenceFixedRow ⟨i.val, top⟩ := dif_pos top
      have bound : (referenceRow before i)[9] < 52 := by
        rw [same]
        simpa only [fixedRow_eq_reference] using fixed_outside_tag ⟨i.val, top⟩ first
      rcases ht with ht | ht | ht <;> omega
  · have tagValue : (referenceRow before i)[9] = 34 := by
      simp only [referenceRow, top]
      rfl
    rw [tagValue] at selected
    rcases ht with ht | ht | ht <;> omega

end Airbender.UnifiedReduced.Setup.Proofs
