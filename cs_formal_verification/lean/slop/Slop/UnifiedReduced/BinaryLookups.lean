import Slop.UnifiedReduced.Setup

namespace Airbender.UnifiedReduced.Setup.Proofs
open Verification
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem wide_lookup [Fact p.Prime] (hp : 256 < p)
    {before : Reference.RiscV.Sail.State} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)} (holds : (Lookup.mk (table before).toRaw entry).Contains env)
    (tag : Nat) (valid : tag = 4 ∨ tag = 6 ∨ tag = 7)
    (selected : entry[9].eval env = (binaryTag tag : ZMod p)) :
    (entry[0].eval env).val < 256 ∧ (entry[1].eval env).val < 256 ∧
      (entry[2].eval env).val < 256 ∧
      BitVec.ofNat 8 (entry[2].eval env).val = byteOperation tag
        (BitVec.ofNat 8 (entry[0].eval env).val) (BitVec.ofNat 8 (entry[1].eval env).val) ∧
      ∀ k : Fin 6, entry[3 + k.val].eval env = 0 := by
  obtain ⟨i, tagged, columns⟩ := lookup_row (by omega : 55 ≤ p) holds (binaryTag tag)
    (by rcases valid with rfl | rfl | rfl <;> decide) selected
  obtain ⟨j, same, oldTag⟩ := wide_region valid tagged
  let oldEntry := (shiftBinopRow j).map (fun (n : Nat) => Expression.const (n : ZMod p))
  have oldHolds : (shiftBinopLookup oldEntry).Contains env := by
    change ∃ k : Fin 524545, oldEntry.map (Expression.eval env) =
      (shiftBinopRow k).map (fun (n : Nat) => (n : ZMod p))
    refine ⟨j, ?_⟩
    simp only [oldEntry, Vector.map_map]
    rfl
  have oldSelected : oldEntry[9].eval env = (tag : ZMod p) := by
    simp only [oldEntry, Vector.getElem_map, Expression.eval, oldTag]
  have result := binary_lookup hp oldHolds tag valid oldSelected
  have value (k : Nat) (bound : k < 9) : entry[k].eval env = ((shiftBinopRow j)[k] : ZMod p) := by
    have col := columns k (by omega)
    rw [same] at col
    simpa only [binaryRow, Vector.getElem_set, show 9 ≠ k by omega, if_false] using col
  simp only [oldEntry, Vector.getElem_map, Expression.eval] at result
  rw [value 0 (by decide), value 1 (by decide), value 2 (by decide)]
  refine ⟨result.1, result.2.1, result.2.2.1, result.2.2.2, ?_⟩
  obtain ⟨key, shape⟩ := binary_row_shape j tag valid oldTag
  intro k
  rw [value (3 + k.val) (by have := k.isLt; omega), shape]
  fin_cases k <;> change ((0 : Nat) : ZMod p) = 0 <;> exact Nat.cast_zero

end Airbender.UnifiedReduced.Setup.Proofs
