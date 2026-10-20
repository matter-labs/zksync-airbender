import Airbender.Proofs.SubwordMemory.NativeLookup

namespace Airbender.SubwordMemory.NativeLookupProofs
open Verification Setup
set_option autoImplicit false

/-- A proved partition of every actual region, including public separator/ROM. -/
inductive Region
  | zero | separator | offset | load | rom | storeClear | storePlace
  deriving DecidableEq

def Region.length : Region → Nat
  | .zero => 1
  | .separator => 65536
  | .offset => 2097152
  | .load => 2097152
  | .rom => 1048576
  | .storeClear => 2097152
  | .storePlace => 2097152

def Region.tag : Region → Nat
  | .zero => 0
  | .separator => 23
  | .offset => 44
  | .load => 45
  | .rom => 46
  | .storeClear => 54
  | .storePlace => 55

def Region.row (rom : WordROM) : (region : Region) → Fin region.length → Vector (ZMod mersenne31Modulus) 4
  | .zero, i => NativeBinary.dataZero.row i
  | .separator, i => ((romSeparatorRow i).map Nat.cast).push 23
  | .offset, i => NativeSubwordOffset.data.row i
  | .load, i => NativeSubwordLoad.data.row i
  | .rom, i => ((rom.alignedRow i).map Nat.cast).push 46
  | .storeClear, i => NativeSubwordStoreClear.data.row i
  | .storePlace, i => NativeSubwordStorePlace.data.row i

/-- Every accepted tagged row comes from a unique native region tag. -/
theorem contains_iff_region (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 4) :
    (NativeSubwordLookup.table rom).Contains #[] query ↔
      ∃ region : Region, ∃ i : Fin region.length, query = region.row rom i := by
  constructor
  · rintro ⟨i, same⟩
    have bound : i.val < 9502721 := i.isLt
    change query = (NativeSubwordLookup.rowNat rom i).map Nat.cast at same
    rw [NativeSubwordLookup.rowNat] at same
    by_cases h0 : i.val < 1
    · rw [dif_pos h0] at same
      refine ⟨.zero, ⟨i.val, by change i.val < 1; omega⟩, ?_⟩
      convert same using 1
      simp only [Region.row, TableData.row]
      rfl
    rw [dif_neg h0] at same
    by_cases h1 : i.val < 65537
    · rw [dif_pos h1] at same
      refine ⟨.separator, ⟨i.val - 1, by change i.val - 1 < 65536; omega⟩, ?_⟩
      convert same using 1
      simp only [Region.row, Vector.map_push, Nat.cast_ofNat]
      rfl
    rw [dif_neg h1] at same
    by_cases h2 : i.val < 2162689
    · rw [dif_pos h2] at same
      refine ⟨.offset, ⟨i.val - 65537, by change i.val - 65537 < 2097152; omega⟩, ?_⟩
      convert same using 1
      simp only [Region.row, TableData.row]
      rfl
    rw [dif_neg h2] at same
    by_cases h3 : i.val < 4259841
    · rw [dif_pos h3] at same
      refine ⟨.load, ⟨i.val - 2162689, by change i.val - 2162689 < 2097152; omega⟩, ?_⟩
      convert same using 1
      simp only [Region.row, TableData.row]
      rfl
    rw [dif_neg h3] at same
    by_cases h4 : i.val < 5308417
    · rw [dif_pos h4] at same
      refine ⟨.rom, ⟨i.val - 4259841, by change i.val - 4259841 < 1048576; omega⟩, ?_⟩
      convert same using 1
      simp only [Region.row, Vector.map_push, Nat.cast_ofNat]
      rfl
    rw [dif_neg h4] at same
    by_cases h5 : i.val < 7405569
    · rw [dif_pos h5] at same
      refine ⟨.storeClear, ⟨i.val - 5308417, by change i.val - 5308417 < 2097152; omega⟩, ?_⟩
      convert same using 1
      simp only [Region.row, TableData.row]
      rfl
    rw [dif_neg h5] at same
    exact ⟨.storePlace, ⟨i.val - 7405569, by change i.val - 7405569 < 2097152; omega⟩, same⟩
  · rintro ⟨region, i, rfl⟩
    cases region with
    | zero => exact zero_region rom i
    | separator => exact separator_region rom i
    | offset => exact offset_region rom i
    | load => exact load_region rom i
    | rom => exact rom_region rom i
    | storeClear => exact store_clear_region rom i
    | storePlace => exact store_place_region rom i

private theorem constant_tag (length tag n : Nat) (bound : n < length) :
    (⟨#[.affine length tag 0]⟩ : Column).get? n = some tag := by
  change getFromBlocks [.affine length tag 0] n = _
  rw [getFromBlocks]
  simp only [Block.length]
  rw [if_pos bound]
  simp [Block.get?, Block.length, bound]

/-- Native literal tag columns and the two public tagged rows fix the selector. -/
theorem region_row_tag (rom : WordROM) (region : Region) (i : Fin region.length) :
    (region.row rom i)[3] = region.tag := by
  cases region with
  | zero =>
    have hi : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
    have column : NativeBinary.dataZero.columns[3].get? i.val = some 0 := by
      change (⟨#[.dense #[0]]⟩ : Column).get? i.val = some 0
      rw [hi]
      decide
    simp only [Region.row, Region.tag, TableData.row, TableData.rowNat,
      Vector.getElem_map, column, Option.getD_some, Nat.cast_zero]
  | separator => simp [Region.row, Region.tag]
  | rom => simp [Region.row, Region.tag]
  | offset =>
    have column : NativeSubwordOffset.data.columns[3].get? i.val = some 44 := by
      change (⟨#[.affine 2097152 44 0]⟩ : Column).get? i.val = some 44
      exact constant_tag 2097152 44 i.val i.isLt
    simp only [Region.row, Region.tag, TableData.row, TableData.rowNat,
      Vector.getElem_map, column, Option.getD_some]

  | load =>
    have column : NativeSubwordLoad.data.columns[3].get? i.val = some 45 := by
      change (⟨#[.affine 2097152 45 0]⟩ : Column).get? i.val = some 45
      exact constant_tag 2097152 45 i.val i.isLt
    simp only [Region.row, Region.tag, TableData.row, TableData.rowNat,
      Vector.getElem_map, column, Option.getD_some]

  | storeClear =>
    have column : NativeSubwordStoreClear.data.columns[3].get? i.val = some 54 := by
      change (⟨#[.affine 2097152 54 0]⟩ : Column).get? i.val = some 54
      exact constant_tag 2097152 54 i.val i.isLt
    simp only [Region.row, Region.tag, TableData.row, TableData.rowNat,
      Vector.getElem_map, column, Option.getD_some]

  | storePlace =>
    have column : NativeSubwordStorePlace.data.columns[3].get? i.val = some 55 := by
      change (⟨#[.affine 2097152 55 0]⟩ : Column).get? i.val = some 55
      exact constant_tag 2097152 55 i.val i.isLt
    simp only [Region.row, Region.tag, TableData.row, TableData.rowNat,
      Vector.getElem_map, column, Option.getD_some]

theorem region_tag_bound (region : Region) : region.tag < mersenne31Modulus := by
  cases region <;> decide

theorem region_tag_injective : Function.Injective Region.tag := by
  intro left right same
  cases left <;> cases right <;> simp_all [Region.tag]

/-- Bounds concern the canonical field selector, derived from actual membership. -/
theorem accepted_selector (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (NativeSubwordLookup.table rom).Contains #[] query) :
    query[3].val ∈ [0,23,44,45,46,54,55] := by
  obtain ⟨region, i, rfl⟩ := (contains_iff_region rom query).mp member
  rw [region_row_tag, ZMod.val_natCast, Nat.mod_eq_of_lt (region_tag_bound region)]
  cases region <;> simp [Region.tag]

/-- The selector uniquely resolves the exact actual region, rather than assuming it. -/
theorem selected_membership (rom : WordROM) (region : Region)
    (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push region.tag) ↔
      ∃ i : Fin region.length, query.push (region.tag : ZMod mersenne31Modulus) =
        region.row rom i := by
  constructor
  · intro member
    obtain ⟨actual, i, same⟩ := (contains_iff_region rom _).mp member
    have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
    have cast_same : (region.tag : ZMod mersenne31Modulus) = actual.tag := by
      simpa only [Vector.getElem_push, Nat.lt_irrefl, ↓reduceDIte, region_row_tag] using tag
    have tags : region.tag = actual.tag := by
      have vals := congrArg ZMod.val cast_same
      simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (region_tag_bound region),
        Nat.mod_eq_of_lt (region_tag_bound actual)] using vals
    cases region_tag_injective tags
    exact ⟨i, same⟩
  · rintro ⟨i, same⟩
    exact (contains_iff_region rom _).mpr ⟨region, i, same⟩

end Airbender.SubwordMemory.NativeLookupProofs
