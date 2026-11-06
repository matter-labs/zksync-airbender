import Airbender.Review.Circuits.ReducedMachine.Tables.Native
import Airbender.Review.Circuits.ReducedMachine.Tables.SignHigh
import Airbender.Proofs.Mersenne31

namespace Airbender.ReducedMachine.NativePoolProofs
open Setup NativeFixed
set_option warningAsError true
set_option Elab.async false

-- Adapt the existing checked ShiftBinop/NativeRegions partition and tag proof.
inductive Region
  | zero | xor | or | and | sign | cleanup | memoryOffset | signFill | conditional | separator | rom | csr | shift | truncate
  deriving DecidableEq

def Region.data : Region → TableData 4
  | .zero => dataT0
  | .xor => dataT4
  | .or => dataT6
  | .and => dataT7
  | .sign => dataT16
  | .cleanup => dataT17
  | .memoryOffset => dataT18
  | .signFill => dataT20
  | .conditional => dataT22
  | .separator => dataT23
  | .rom => dataT24
  | .csr => dataT25
  | .shift => dataT37
  | .truncate => dataT47

def Region.tag : Region → Nat
  | .zero => 0
  | .xor => 4
  | .or => 6
  | .and => 7
  | .sign => 16
  | .cleanup => 17
  | .memoryOffset => 18
  | .signFill => 20
  | .conditional => 22
  | .separator => 23
  | .rom => 24
  | .csr => 25
  | .shift => 37
  | .truncate => 47

/-- Every accepted full-pool row resolves to one actual stored region. -/
theorem member_region (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query) :
    ∃ region : Region, ∃ i : Fin region.data.length, query = region.data.row i := by
  obtain ⟨i,same⟩ := member
  change query = (rowNat i).map Nat.cast at same
  rw [rowNat] at same
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

private theorem constant_tag (length tag n : Nat) (bound : n < length) :
    (⟨#[.affine length tag 0]⟩ : Column).get? n = some tag := by
  change getFromBlocks [.affine length tag 0] n = _
  rw [getFromBlocks]
  simp only [Block.length]
  rw [if_pos bound]
  simp [Block.get?,Block.length,bound]

theorem region_row_tag (region : Region) (i : Fin region.data.length) :
    (region.data.row i : Vector (ZMod mersenne31Modulus) 4)[3] = region.tag := by
  have column : region.data.columns[3].get? i.val = some region.tag := by
    cases region with
    | zero =>
      have zero : i.val = 0 := by have bound := i.isLt; change i.val < 1 at bound; omega
      change (⟨#[.dense #[0]]⟩ : Column).get? i.val = some 0
      rw [zero]
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
    | sign =>
      change (⟨#[.affine 65536 16 0]⟩ : Column).get? i.val = some 16
      exact constant_tag 65536 16 i.val i.isLt
    | cleanup =>
      change (⟨#[.affine 65536 17 0]⟩ : Column).get? i.val = some 17
      exact constant_tag 65536 17 i.val i.isLt
    | memoryOffset =>
      change (⟨#[.affine 65536 18 0]⟩ : Column).get? i.val = some 18
      exact constant_tag 65536 18 i.val i.isLt
    | signFill =>
      change (⟨#[.affine 128 20 0]⟩ : Column).get? i.val = some 20
      exact constant_tag 128 20 i.val i.isLt
    | conditional =>
      change (⟨#[.affine 128 22 0]⟩ : Column).get? i.val = some 22
      exact constant_tag 128 22 i.val i.isLt
    | separator =>
      change (⟨#[.affine 65536 23 0]⟩ : Column).get? i.val = some 23
      exact constant_tag 65536 23 i.val i.isLt
    | rom =>
      change (⟨#[.affine 1048576 24 0]⟩ : Column).get? i.val = some 24
      exact constant_tag 1048576 24 i.val i.isLt
    | csr =>
      change (⟨#[.affine 4096 25 0]⟩ : Column).get? i.val = some 25
      exact constant_tag 4096 25 i.val i.isLt
    | shift =>
      change (⟨#[.affine 4194304 37 0]⟩ : Column).get? i.val = some 37
      exact constant_tag 4194304 37 i.val i.isLt
    | truncate =>
      change (⟨#[.affine 65536 47 0]⟩ : Column).get? i.val = some 47
      exact constant_tag 65536 47 i.val i.isLt
  simp only [TableData.row,TableData.rowNat,Vector.getElem_map,column,Option.getD_some]

theorem tag_bound (region : Region) : region.tag < mersenne31Modulus := by
  cases region <;> decide

/-- A full-pool member cannot use a tag absent from the actual native registry. -/
theorem accepted_selector (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query) :
    query[3].val ∈ NativeFixed.tags := by
  obtain ⟨region,i,rfl⟩ := member_region query member
  rw [region_row_tag,ZMod.val_natCast,Nat.mod_eq_of_lt (tag_bound region)]
  cases region <;> simp [Region.tag,NativeFixed.tags]

theorem shared_sign_data : dataT16 = SignHigh.data := rfl

/-- Native tag isolation recovers the previously certified literal sign region. -/
theorem sign_member (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = 16) : SignHigh.Contains query := by
  obtain ⟨region,i,same⟩ := member_region query member
  have tag := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[3]) same
  rw [region_row_tag] at tag
  have sameTag : (region.tag : ZMod mersenne31Modulus) = Region.sign.tag :=
    tag.symm.trans selected
  have values := congrArg ZMod.val sameTag
  have tags : region.tag = Region.sign.tag := by
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (tag_bound region),
      Nat.mod_eq_of_lt (tag_bound .sign)] using values
  have actual : region = .sign := by cases region <;> simp_all [Region.tag]
  subst region
  exact ⟨i,by simpa only [Region.data,shared_sign_data] using same⟩

end Airbender.ReducedMachine.NativePoolProofs
