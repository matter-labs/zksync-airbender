import Airbender.Proofs.ShiftBinop.NativeLookup

namespace Airbender.ShiftBinop.NativeLookupProofs
open Verification Setup
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- A partition of the actual stored regions, not a table-equivalence premise. -/
inductive Region
  | zero | xor | or | and | csr | truncate | sllLow | sllHigh | srlLow | srlHigh | signFill | range
  deriving DecidableEq

def Region.data : Region → TableData 4
  | .zero => NativeBinary.dataZero
  | .xor => NativeBinary.dataXor
  | .or => NativeBinary.dataOr
  | .and => NativeBinary.dataAnd
  | .csr => NativeShiftCsr.data
  | .truncate => NativeShiftScalars.dataTruncate
  | .sllLow => NativeSllLow.data
  | .sllHigh => NativeSllHigh.data
  | .srlLow => NativeSrlLow.data
  | .srlHigh => NativeSrlHigh.data
  | .signFill => NativeShiftScalars.dataSignFill
  | .range => NativeShiftScalars.dataRange

def Region.tag : Region → Nat
  | .zero => 0
  | .xor => 4
  | .or => 6
  | .and => 7
  | .csr => 25
  | .truncate => 47
  | .sllLow => 48
  | .sllHigh => 49
  | .srlLow => 50
  | .srlHigh => 51
  | .signFill => 52
  | .range => 53

/-- Exact decomposition of the native table; the selector is still part of the row. -/
theorem contains_iff_region (query : Vector (ZMod mersenne31Modulus) 4) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] query ↔
      ∃ region : Region, ∃ i : Fin region.data.length, query = region.data.row i := by
  constructor
  · rintro ⟨i, same⟩
    change query = (NativeShiftLookup.rowNat i).map Nat.cast at same
    rw [NativeShiftLookup.rowNat] at same
    by_cases h0 : i.val < 1
    · rw [dif_pos h0] at same
      exact ⟨.zero, _, same⟩
    rw [dif_neg h0] at same
    by_cases h1 : i.val < 65537
    · rw [dif_pos h1] at same
      exact ⟨.xor, _, same⟩
    rw [dif_neg h1] at same
    by_cases h2 : i.val < 131073
    · rw [dif_pos h2] at same
      exact ⟨.or, _, same⟩
    rw [dif_neg h2] at same
    by_cases h3 : i.val < 196609
    · rw [dif_pos h3] at same
      exact ⟨.and, _, same⟩
    rw [dif_neg h3] at same
    by_cases h4 : i.val < 200705
    · rw [dif_pos h4] at same
      exact ⟨.csr, _, same⟩
    rw [dif_neg h4] at same
    by_cases h5 : i.val < 266241
    · rw [dif_pos h5] at same
      exact ⟨.truncate, _, same⟩
    rw [dif_neg h5] at same
    by_cases h6 : i.val < 2363393
    · rw [dif_pos h6] at same
      exact ⟨.sllLow, _, same⟩
    rw [dif_neg h6] at same
    by_cases h7 : i.val < 4460545
    · rw [dif_pos h7] at same
      exact ⟨.sllHigh, _, same⟩
    rw [dif_neg h7] at same
    by_cases h8 : i.val < 6557697
    · rw [dif_pos h8] at same
      exact ⟨.srlLow, _, same⟩
    rw [dif_neg h8] at same
    by_cases h9 : i.val < 8654849
    · rw [dif_pos h9] at same
      exact ⟨.srlHigh, _, same⟩
    rw [dif_neg h9] at same
    by_cases h10 : i.val < 10752001
    · rw [dif_pos h10] at same
      exact ⟨.signFill, _, same⟩
    rw [dif_neg h10] at same
    exact ⟨.range, _, same⟩
  · rintro ⟨region, i, rfl⟩
    cases region with
    | zero => exact zero_region i
    | xor => exact xor_region i
    | or => exact or_region i
    | and => exact and_region i
    | csr => exact csr_region i
    | truncate => exact truncate_region i
    | sllLow => exact sll_low_region i
    | sllHigh => exact sll_high_region i
    | srlLow => exact srl_low_region i
    | srlHigh => exact srl_high_region i
    | signFill => exact sign_fill_region i
    | range => exact range_region i

private theorem constant_tag (length tag n : Nat) (bound : n < length) :
    (⟨#[.affine length tag 0]⟩ : Column).get? n = some tag := by
  change getFromBlocks [.affine length tag 0] n = _
  rw [getFromBlocks]
  simp only [Block.length]
  rw [if_pos bound]
  simp [Block.get?, Block.length, bound]

/-- The fourth stored column fixes the tag in every region. -/
theorem region_row_tag (region : Region) (i : Fin region.data.length) :
    (region.data.row i : Vector (ZMod mersenne31Modulus) 4)[3] = region.tag := by
  have column : region.data.columns[3].get? i.val = some region.tag := by
    cases region with
    | zero =>
      have hi : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
      change (⟨#[.dense #[0]]⟩ : Column).get? i.val = some 0
      rw [hi]
      decide
    | xor =>
      change (⟨#[.affine 65536 4 0]⟩ : Column).get? i.val = some 4
      exact constant_tag 65536 4 i.val i.isLt
    | or =>
      change (⟨#[.affine 65536 6 0]⟩ : Column).get? i.val = some 6
      exact constant_tag 65536 6 i.val i.isLt
    | and =>
      change (⟨#[.affine 65536 7 0]⟩ : Column).get? i.val = some 7
      exact constant_tag 65536 7 i.val i.isLt
    | csr =>
      change (⟨#[.affine 4096 25 0]⟩ : Column).get? i.val = some 25
      exact constant_tag 4096 25 i.val i.isLt
    | truncate =>
      change (⟨#[.affine 65536 47 0]⟩ : Column).get? i.val = some 47
      exact constant_tag 65536 47 i.val i.isLt
    | sllLow =>
      change (⟨#[.affine 2097152 48 0]⟩ : Column).get? i.val = some 48
      exact constant_tag 2097152 48 i.val i.isLt
    | sllHigh =>
      change (⟨#[.affine 2097152 49 0]⟩ : Column).get? i.val = some 49
      exact constant_tag 2097152 49 i.val i.isLt
    | srlLow =>
      change (⟨#[.affine 2097152 50 0]⟩ : Column).get? i.val = some 50
      exact constant_tag 2097152 50 i.val i.isLt
    | srlHigh =>
      change (⟨#[.affine 2097152 51 0]⟩ : Column).get? i.val = some 51
      exact constant_tag 2097152 51 i.val i.isLt
    | signFill =>
      change (⟨#[.affine 2097152 52 0]⟩ : Column).get? i.val = some 52
      exact constant_tag 2097152 52 i.val i.isLt
    | range =>
      change (⟨#[.affine 65536 53 0]⟩ : Column).get? i.val = some 53
      exact constant_tag 65536 53 i.val i.isLt
  simp only [TableData.row, TableData.rowNat, Vector.getElem_map, column, Option.getD_some]

theorem region_tag_bound (region : Region) : region.tag < mersenne31Modulus := by
  cases region <;> decide

theorem region_tag_injective : Function.Injective Region.tag := by
  intro left right same
  cases left <;> cases right <;> simp_all [Region.tag]

/-- No unsupported tag can enter through a different actual region. -/
theorem accepted_selector (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] query) :
    query[3].val = 0 ∨ query[3].val = 4 ∨ query[3].val = 6 ∨ query[3].val = 7 ∨
      query[3].val = 25 ∨ query[3].val = 47 ∨ query[3].val = 48 ∨ query[3].val = 49 ∨
      query[3].val = 50 ∨ query[3].val = 51 ∨ query[3].val = 52 ∨ query[3].val = 53 := by
  obtain ⟨region, i, rfl⟩ := (contains_iff_region query).mp member
  rw [region_row_tag, ZMod.val_natCast, Nat.mod_eq_of_lt (region_tag_bound region)]
  cases region <;> simp [Region.tag]

/-- A selected tag resolves to exactly that region's literal stored membership. -/
theorem selected_membership (region : Region) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push region.tag) ↔
      ∃ i : Fin region.data.length, query.push (region.tag : ZMod mersenne31Modulus) =
        region.data.row i := by
  constructor
  · intro member
    obtain ⟨actual, i, same⟩ := (contains_iff_region _).mp member
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
    exact (contains_iff_region _).mpr ⟨region, i, same⟩

end Airbender.ShiftBinop.NativeLookupProofs
