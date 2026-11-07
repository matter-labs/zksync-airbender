import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimePool
import Airbender.Proofs.ReducedMachine.NativePool

namespace Airbender.ReducedMachine.NativeRuntimePoolProofs
open Setup NativeFixed NativeRuntimePool
set_option warningAsError true
set_option Elab.async false

abbrev Region := NativePoolProofs.Region

/-- Reuse actual stored regions; only the separately exported CSR input changes. -/
def regionData (region : Region) : TableData 4 :=
  if region = .csr then NativeRuntimeCSR.data else region.data

theorem unchanged_region (region : Region) (other : region ≠ .csr) :
    regionData region = region.data := if_neg other

/-- Every accepted full-pool row resolves to one actual stored region. -/
theorem member_region (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] query) :
    ∃ region : Region, ∃ i : Fin (regionData region).length, query = (regionData region).row i := by
  obtain ⟨i,same⟩ := member
  change query = (NativeRuntimePool.rowNat i).map Nat.cast at same
  rw [NativeRuntimePool.rowNat] at same
  by_cases h0 : i.val < 1
  · rw [dif_pos h0] at same
    exact ⟨.zero,_,same⟩
  rw [dif_neg h0] at same
  by_cases h1 : i.val < 65537
  · rw [dif_pos h1] at same
    exact ⟨.xor,_,same⟩
  rw [dif_neg h1] at same
  by_cases h2 : i.val < 131073
  · rw [dif_pos h2] at same
    exact ⟨.or,_,same⟩
  rw [dif_neg h2] at same
  by_cases h3 : i.val < 196609
  · rw [dif_pos h3] at same
    exact ⟨.and,_,same⟩
  rw [dif_neg h3] at same
  by_cases h4 : i.val < 262145
  · rw [dif_pos h4] at same
    exact ⟨.sign,_,same⟩
  rw [dif_neg h4] at same
  by_cases h5 : i.val < 327681
  · rw [dif_pos h5] at same
    exact ⟨.cleanup,_,same⟩
  rw [dif_neg h5] at same
  by_cases h6 : i.val < 393217
  · rw [dif_pos h6] at same
    exact ⟨.memoryOffset,_,same⟩
  rw [dif_neg h6] at same
  by_cases h7 : i.val < 393345
  · rw [dif_pos h7] at same
    exact ⟨.signFill,_,same⟩
  rw [dif_neg h7] at same
  by_cases h8 : i.val < 393473
  · rw [dif_pos h8] at same
    exact ⟨.conditional,_,same⟩
  rw [dif_neg h8] at same
  by_cases h9 : i.val < 459009
  · rw [dif_pos h9] at same
    exact ⟨.separator,_,same⟩
  rw [dif_neg h9] at same
  by_cases h10 : i.val < 1507585
  · rw [dif_pos h10] at same
    exact ⟨.rom,_,same⟩
  rw [dif_neg h10] at same
  by_cases h11 : i.val < 1511681
  · rw [dif_pos h11] at same
    exact ⟨.csr,_,same⟩
  rw [dif_neg h11] at same
  by_cases h12 : i.val < 5705985
  · rw [dif_pos h12] at same
    exact ⟨.shift,_,same⟩
  rw [dif_neg h12] at same
  exact ⟨.truncate,_,same⟩

theorem region_row_tag (region : Region) (i : Fin (regionData region).length) :
    ((regionData region).row i : Vector (ZMod mersenne31Modulus) 4)[3] = region.tag := by
  cases region with
  | zero => exact NativePoolProofs.region_row_tag .zero i
  | xor => exact NativePoolProofs.region_row_tag .xor i
  | or => exact NativePoolProofs.region_row_tag .or i
  | and => exact NativePoolProofs.region_row_tag .and i
  | sign => exact NativePoolProofs.region_row_tag .sign i
  | cleanup => exact NativePoolProofs.region_row_tag .cleanup i
  | memoryOffset => exact NativePoolProofs.region_row_tag .memoryOffset i
  | signFill => exact NativePoolProofs.region_row_tag .signFill i
  | conditional => exact NativePoolProofs.region_row_tag .conditional i
  | separator => exact NativePoolProofs.region_row_tag .separator i
  | rom => exact NativePoolProofs.region_row_tag .rom i
  | shift => exact NativePoolProofs.region_row_tag .shift i
  | truncate => exact NativePoolProofs.region_row_tag .truncate i
  | csr =>
    have bound : i.val < 4096 := i.isLt
    have column : (regionData .csr).columns[3].get? i.val = some 25 := by
      change (⟨#[.affine 4096 25 0]⟩ : Column).get? i.val = some 25
      change getFromBlocks [.affine 4096 25 0] i.val = _
      rw [getFromBlocks]
      simp only [Block.length]
      rw [if_pos bound]
      simp [Block.get?,Block.length,bound]
    simp only [TableData.row,TableData.rowNat,Vector.getElem_map,column,Option.getD_some]
    rfl

/-- All actual fourth columns still isolate the native tag registry. -/
theorem accepted_selector (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] query) :
    query[3].val ∈ NativeRuntimePool.tags := by
  obtain ⟨region,i,rfl⟩ := member_region query member
  rw [region_row_tag,ZMod.val_natCast,Nat.mod_eq_of_lt (NativePoolProofs.tag_bound region)]
  cases region <;> simp [NativePoolProofs.Region.tag,NativeRuntimePool.tags,NativeFixed.tags]

/-- The actual stored fourth column isolates any selected native region. -/
theorem selected_region (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] query)
    (region : Region) (selected : query[3] = region.tag) :
    ∃ i : Fin (regionData region).length, query = (regionData region).row i := by
  obtain ⟨actual,i,same⟩ := member_region query member
  have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
  rw [region_row_tag] at tag
  have sameTag : (actual.tag : ZMod mersenne31Modulus) = region.tag :=
    tag.symm.trans selected
  have values := congrArg ZMod.val sameTag
  have tags : actual.tag = region.tag := by
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (NativePoolProofs.tag_bound actual),
      Nat.mod_eq_of_lt (NativePoolProofs.tag_bound region)] using values
  have identical := NativePoolProofs.tag_injective tags
  subst actual
  exact ⟨i,same⟩

/-- The unchanged actual tag16 data is recovered by this pool's tag isolation. -/
theorem sign_member (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 16) : SignHigh.Contains query := by
  obtain ⟨i,same⟩ := selected_region query member .sign selected
  exact ⟨i,same⟩

/-- Runtime CSR membership comes from the new stored region, not the old fixture. -/
theorem csr_member (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (NativeRuntimePool.table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 25) : NativeRuntimeCSR.Contains query := by
  obtain ⟨i,same⟩ := selected_region query member .csr selected
  exact ⟨i,same⟩
end Airbender.ReducedMachine.NativeRuntimePoolProofs
