import Airbender.Review.Helpers.Tables.NativeSmallRangeData
import Airbender.Proofs.Tables.SmallRange
import Airbender.Proofs.Tables.PeriodicColumns
import Mathlib.Tactic.IntervalCases

namespace Airbender.MulDiv.Proofs
open Setup Verification

-- Both helper declarations are copied unchanged from the checked v2 control certificate.
private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

/-- All 65,536 actual native rows, including tag eight, proved symbolically
    from stored periodic columns; no row-by-row certificate or equivalence premise. -/
theorem native_small_range_rows (i : Fin 65536) :
    NativeSmallRange.data.rowNat i = (smallRangeRow i).push 8 := by
  have first : NativeSmallRange.data.columns[0].get? i.val = some (i.val / 256) := by
    change (⟨#[.periodic 256 1 (Array.replicate 256 0)]⟩ : Column).get? i.val = _
    have inside : i.val < 256 * (Array.replicate 256 0).size := by simpa only [Array.size_replicate] using i.isLt
    refine (single_get (.periodic 256 1 (Array.replicate 256 0)) i.val inside).trans ?_
    have read := Setup.Proofs.periodic_get (Array.replicate 256 0) 256 1 i.val (by simp only [Array.size_replicate]; decide) inside
    change Block.get? (.periodic 256 1 (Array.replicate 256 0)) i.val = _ at read
    rw [read]
    simp
  have second : NativeSmallRange.data.columns[1].get? i.val = some (i.val % 256) := by
    change (⟨#[.periodic 256 0 (Array.range 256)]⟩ : Column).get? i.val = _
    have inside : i.val < 256 * (Array.range 256).size := by simpa only [Array.size_range] using i.isLt
    refine (single_get (.periodic 256 0 (Array.range 256)) i.val inside).trans ?_
    have read := Setup.Proofs.periodic_get (Array.range 256) 256 0 i.val (by simp only [Array.size_range]; decide) inside
    change Block.get? (.periodic 256 0 (Array.range 256)) i.val = _ at read
    rw [read]
    simp
  have zero : NativeSmallRange.data.columns[2].get? i.val = some 0 := by
    change (⟨#[.affine 65536 0 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 0 0 i.val i.isLt
  have tag : NativeSmallRange.data.columns[3].get? i.val = some 8 := by
    change (⟨#[.affine 65536 8 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 8 0 i.val i.isLt
  ext lane bound
  interval_cases lane <;> simp [TableData.rowNat, first, second, zero, tag, smallRangeRow]

/-- Exact Clean membership agrees with the tagged native exported rows. -/
theorem native_small_range_lookup (query : Vector (ZMod mersenne31Modulus) 3) :
    smallRangeTable.Contains #[] query ↔ ∃ i : Fin 65536,
      query.push 8 = NativeSmallRange.data.row i := by
  change (∃ i : Fin 65536, query = (smallRangeRow i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [TableData.row, native_small_range_rows, Vector.map_push]⟩
  · rintro ⟨i, same⟩
    refine ⟨i, ?_⟩
    ext lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [TableData.row, native_small_range_rows, Vector.map_push,
      Vector.getElem_push, bound] using selected

end Airbender.MulDiv.Proofs
