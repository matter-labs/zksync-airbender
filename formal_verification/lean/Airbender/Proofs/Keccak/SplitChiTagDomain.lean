import Airbender.Proofs.Keccak.SplitControlTags
import Airbender.Proofs.Keccak.SplitChiNativeLookup

namespace Airbender.Keccak.Split.Native.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false
variable [Fact babyBearModulus.Prime]

omit [Fact babyBearModulus.Prime] in
private theorem tag_column : Fixed.chi5Generic.columns[10] =
    ⟨#[.affine 1048576 65 0, .affine 121 66 0, .affine 3145607 0 0]⟩ := by rfl

/-- The original chi5 reference contains only its two real table tags. -/
theorem chi5_reference_row_tag (index : Fin Fixed.chi5Generic.length) :
    (((Fixed.chi5Generic.row index).map (fun value : Int => (value : ZMod babyBearModulus)))[10] = 65) ∨
    (((Fixed.chi5Generic.row index).map (fun value : Int => (value : ZMod babyBearModulus)))[10] = 66) := by
  have bound : index.val < 1048697 := index.isLt
  simp only [TableData.row, Vector.getElem_map]
  change (signedValue ((Fixed.chi5Generic.columns[10].get? (0 + index.val)).getD 0) : ZMod babyBearModulus) = 65 ∨
    (signedValue ((Fixed.chi5Generic.columns[10].get? (0 + index.val)).getD 0) : ZMod babyBearModulus) = 66
  rw [Nat.zero_add, tag_column]
  simp only [Column.get?, getFromBlocks, Block.get?, Block.length]
  split_ifs
  all_goals try simp only [zero_mul, add_zero, Option.getD_some, Option.getD_none,
    Int.toNat_natCast, signedValue_cast]
  all_goals first | omega | left; rfl | right; rfl

theorem chi5_reference_tag (row : Vector (ZMod babyBearModulus) 11)
    (member : chi5FixedTable.toRaw.Contains #[] row) : row[10] = 65 ∨ row[10] = 66 := by
  change ∃ index : Fin Fixed.chi5Generic.length,
    row = (Fixed.chi5Generic.row index).map (fun value : Int => (value : ZMod babyBearModulus)) at member
  obtain ⟨index, rfl⟩ := member
  exact chi5_reference_row_tag index

theorem chi5_reference_excludes_zero :
    ¬ chi5FixedTable.toRaw.Contains #[] (Vector.replicate 11 0) := by
  intro member
  have tag := chi5_reference_tag _ member
  change (0 : ZMod babyBearModulus) = 65 ∨ (0 : ZMod babyBearModulus) = 66 at tag
  rcases tag with tag | tag
  · have value := congrArg ZMod.val tag
    change 0 = 65 at value
    omega
  · have value := congrArg ZMod.val tag
    change 0 = 66 at value
    omega

end Airbender.Keccak.Split.Native.Proofs
