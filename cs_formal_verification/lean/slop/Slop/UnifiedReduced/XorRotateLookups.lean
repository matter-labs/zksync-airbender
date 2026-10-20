import Slop.UnifiedReduced.Setup

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

theorem rotate_region {before : Reference.RiscV.Sail.State} {i : Fin 2097537} {tag : Nat}
    (lower : 47 ≤ tag) (upper : tag < 51) (selected : (row before i)[9] = tag) :
    ∃ j : Fin 262144, row before i = rotateRow j ∧ 47 + j.val / 65536 = tag := by
  by_cases top : i.val < 1048961
  · by_cases first : i.val < 524545
    · have same : row before i = binaryRow ⟨i.val, first⟩ := by
        simp only [row, top, dif_pos, fixedRow, first]
      rw [same] at selected
      have bound := shift_tag_bound ⟨i.val, first⟩
      simp only [binaryRow, Vector.getElem_set_self] at selected
      unfold binaryTag at selected
      split_ifs at selected <;> omega
    · have same : row before i = fixedRow ⟨i.val, top⟩ := dif_pos top
      rw [same] at selected
      unfold fixedRow at selected
      dsimp only at selected
      split at selected
      · contradiction
      · split at selected
        · change 1 = tag at selected; omega
        · split at selected
          · change 5 = tag at selected; omega
          · split at selected
            · change 2 = tag at selected; omega
            · split at selected
              · change 51 = tag at selected; omega
              · rename_i last
                have jBound : i.val - 786817 < 262144 := by omega
                refine ⟨⟨i.val - 786817, jBound⟩, ?_, selected⟩
                rw [same]
                simp only [fixedRow]
                split_ifs; first | omega | rfl
  · have value : (row before i)[9] = 34 := by
      simp only [row, top]
      rfl
    omega

theorem rotate_lookup [Fact p.Prime] (hp : 256 < p)
    {before : Reference.RiscV.Sail.State} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)} (holds : (Lookup.mk (table before).toRaw entry).Contains env)
    (tag : Nat) (lower : 47 ≤ tag) (upper : tag < 51)
    (selected : entry[9].eval env = (tag : ZMod p)) :
    ∃ kind : Fin 4, kind.val = tag - 47 ∧
      (entry[0].eval env).val < 256 ∧ (entry[1].eval env).val < 256 ∧
      ∀ byte : Fin 4, entry[2 + byte.val].eval env =
        (((BitVec.ofNat 32 ((entry[0].eval env).val ^^^ (entry[1].eval env).val)).rotateRight
          (#[16, 12, 8, 7][kind.val]!)).extractLsb' (8 * byte.val) 8).toNat := by
  obtain ⟨i, tagged, columns⟩ := lookup_row (by omega : 55 ≤ p) holds tag (by omega) selected
  obtain ⟨j, same, tagValue⟩ := rotate_region lower upper tagged
  have shape (k : Nat) (bound : k < 10) := columns k bound
  have left := shape 0 (by decide)
  have right := shape 1 (by decide)
  rw [same] at left right
  change entry[0].eval env = ((j.val / 256 % 256 : Nat) : ZMod p) at left
  change entry[1].eval env = ((j.val % 256 : Nat) : ZMod p) at right
  have lb : j.val / 256 % 256 < 256 := Nat.mod_lt _ (by decide)
  have rb : j.val % 256 < 256 := Nat.mod_lt _ (by decide)
  have lv : (entry[0].eval env).val = j.val / 256 % 256 := by
    rw [left, ZMod.val_natCast_of_lt (by omega)]
  have rv : (entry[1].eval env).val = j.val % 256 := by
    rw [right, ZMod.val_natCast_of_lt (by omega)]
  refine ⟨⟨j.val / 65536, by have := j.isLt; omega⟩, ?_, lv ▸ lb, rv ▸ rb, ?_⟩
  · change j.val / 65536 = tag - 47
    omega
  intro byte
  rw [lv, rv]
  have value := shape (2 + byte.val) (by have := byte.isLt; omega)
  rw [same] at value
  fin_cases byte
  all_goals simpa [rotateRow, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] using value

end Airbender.UnifiedReduced.Setup.Proofs
